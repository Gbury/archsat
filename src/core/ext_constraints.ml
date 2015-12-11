
let section = Util.Section.make ~parent:Dispatcher.section "constraints"

(* Options *)
(* ************************************************************************ *)

type unif_algo =
  | Nope
  | Unif_depth
  | Unif_breadth

let unif_algo = ref Nope

let need_restart = ref false

let kind_list = [
    "none", Nope;
    "unif_d", Unif_depth;
    "unif_b", Unif_breadth;
  ]

let parse_kind = Cmdliner.Arg.enum kind_list

(* Accumulators for constraints *)
(* ************************************************************************ *)

type zero
type succ

type constraints = (Unif.t, Ext_meta.state) Constraints.t

type _ acc =
  | Empty : zero acc
  | Acc : _ acc * constraints -> succ acc
(* A type for constraints accumulators. the type parameter indicates wether
   the constraint is empty or not.
   Acc(acc, l, c) is so that c is the enumeration of constraints
   that satisfy acc, and induce a contradiction in some formuylas of l *)

type t = {
  id : int;
  acc : succ acc;
}
(* Accumulators are tagged with an increasing id in order to know which accumulator
   is more recent when comparing two *)

let rec belong : type l. succ acc -> l acc -> bool =
  fun a b -> match b with
    | Empty -> false
    | Acc (a', _) -> a == b || belong a a'
(* We test wether a non-empty acc is a sub-accumulator of another accumulator
   (which can possibly be empty). *)

let make =
  let c = ref 0 in
  (fun acc -> incr c; { id = !c; acc })

(* Builtin symbol *)
(* ************************************************************************ *)

type Expr.builtin += Acc of t

let make_builtin acc =
  let builtin = Acc acc in
  let p = Expr.Id.term_fun ~builtin (Format.sprintf "acc#%d" acc.id) [] [] Expr.Ty.prop in
  Expr.Formula.pred (Expr.Term.apply p [] [])


(* Accumulators *)
(* ************************************************************************ *)

let empty =
  let fold g _ = g in
  match Constraints.make (Gen.singleton Unif.empty) fold with
  | Some c -> c
  | None -> assert false

let gen_of_state st =
  let open Ext_meta in
  Gen.(
    append
      (of_list st.inequalities)
      (product (of_list st.true_preds) (of_list st.false_preds))
  )

let unif_depth =
  let fold g st =
    Gen.flat_map (fun s ->
        Gen.filter_map (fun (t, t') ->
            try Some (Unif.Robinson.term s t t')
            with Unif.Robinson.Impossible_ty _ | Unif.Robinson.Impossible_term _ -> None
          ) (gen_of_state st)) g
  in
  match Constraints.make (Gen.singleton Unif.empty) fold with
  | Some x -> x
  | None -> assert false

let unif_breadth =
  let gen st =
    Gen.filter_map (fun (t, t') -> Unif.Robinson.find ~section t t') (gen_of_state st)
  in
  let merger (t, t') = match Unif.combine t t' with
    | Some s -> Gen.singleton s
    | None -> (fun () -> None)
  in
  Constraints.from_merger gen merger (Gen.singleton Unif.empty)

let gen_of_acc : type a. a acc -> constraints = function
  | Acc (_, g) -> g
  | Empty -> begin match !unif_algo with
      | Nope -> empty
      | Unif_depth -> unif_depth
      | Unif_breadth -> unif_breadth
    end

(* Parsing entry formulas *)
(* ************************************************************************ *)

let parse iter =
  let acc = ref None in
  let st = Ext_meta.empty_st () in
  let aux = function
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred { Expr.term = Expr.App ({ Expr.builtin = Acc t }, _, _) } } } ->
      ()
    | { Expr.formula = Expr.Pred { Expr.term = Expr.App ({ Expr.builtin = Acc t }, _, _) } } ->
      begin match !acc with
        | None -> acc := Some t
        | Some t' ->
          let new_acc =
            if t.id > t'.id then (assert (belong t'.acc t.acc); t)
            else                 (assert (belong t.acc t'.acc); t')
          in
          acc := Some new_acc
      end
    | f -> Ext_meta.parse_aux st f
  in
  let () = iter aux in
  !acc, st

module H = Hashtbl.Make(Expr.Formula)

let tmp = H.create 2500

let handle_aux iter acc st =
  let c = gen_of_acc acc in
  Ext_meta.debug_st 30 st;
  match Constraints.add_constraint c st with
  | Some c' ->
    Util.debug ~section 5 "New constraint";
    Util.debug ~section 10 "Clause :";
    List.iter (fun f -> Util.debug ~section 10 "  - %a" Expr.Debug.formula (Expr.Formula.neg f)) st.Ext_meta.formulas;
    let f = Expr.Formula.f_or (List.map Expr.Formula.neg st.Ext_meta.formulas) in
    if H.mem tmp f then assert false
    else H.add tmp f 0;
    Solver.assume [
      List.map Expr.Formula.neg st.Ext_meta.formulas;
      [make_builtin (make (Acc (acc, c')))];
    ]
  | None ->
    Util.debug ~section 2 "Couldn't find a satisfiable constraint";
    if !Ext_meta.meta_start + 1 < !Ext_meta.meta_max then begin
      need_restart := true;
      if !Ext_meta.meta_start < !Ext_meta.meta_max then begin
        incr Ext_meta.meta_start;
        Ext_meta.iter Ext_meta.do_formula
      end;
      Util.debug ~section 2 "Adding new meta (total: %d)" !Ext_meta.meta_start
    end;
    raise Solver.Restart

let branches_closed = ref 0

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dispatcher.If_sat iter ->
    begin match parse iter with
      | None, st ->
        Util.debug ~section 5 "Generating empty constraint";
        handle_aux iter Empty st
      | Some t, st ->
        Util.debug ~section 10 "Found previous constraint";
        handle_aux iter t.acc st
    end;
    incr branches_closed;
    Util.debug ~section 0 "Closed %d branches" !branches_closed;
    Some ()
  | Solver.Found _ ->
    branches_closed := 0;
    if !need_restart then begin
      need_restart := false;
      Some Solver.Ok
    end else
      None
  | _ -> None

(* Evaluating *)
(* ************************************************************************ *)

let eval = function
  | { Expr.formula = Expr.Pred { Expr.term = Expr.App ({ Expr.builtin = Acc _ }, _, _) } } -> Some (false, 0)
  | _ -> None

let options =
  let docs = Options.ext_sect in
  let kind =
    let doc = CCPrint.sprintf "The constraint generation method to use,
    $(docv) may be %s" (Cmdliner.Arg.doc_alts_enum ~quoted:false kind_list) in
    Cmdliner.Arg.(value & opt parse_kind Nope & info ["cstr.kind"] ~docv:"METHOD" ~docs ~doc)
  in
  let aux kind =
    unif_algo := kind
  in
  Cmdliner.Term.(pure aux $ kind)

;;
Dispatcher.Plugin.register "constraints" ~options
  ~descr:"Handles instanciation using constraints to close multiple branches at the same time"
  (Dispatcher.mk_ext ~section
     ~handle:{Dispatcher.handle=handle}
     ~eval_pred:eval ())

