
let section = Util.Section.make ~parent:Dispatcher.section "cstr"

(* Options *)
(* ************************************************************************ *)

type unif_algo =
  | Unif_depth
  | Unif_breadth

let unif_algo = ref Unif_depth

let need_restart = ref false

let kind_list = [
    "unif_d", Unif_depth;
    "unif_b", Unif_breadth;
  ]

let parse_kind = Cmdliner.Arg.enum kind_list

(* Dumping dot graphs *)
(* ************************************************************************ *)

let to_dump = ref []

let dump_acc t = match !to_dump with
  | [] -> to_dump := [t]
  | _ :: r -> to_dump := t :: r

let dump_new_acc t =
  to_dump := t :: !to_dump

let pp_unif fmt u =
  if Unif.(equal u empty) then Format.fprintf fmt "\\<empty\\>";
  Expr.Subst.iter (fun m ty ->
      Format.fprintf fmt "%a --\\> %a\\n" Expr.Print.meta m Expr.Print.ty ty)
    u.Unif.ty_map;
  Expr.Subst.iter (fun m t ->
      Format.fprintf fmt "%a --\\> %a\\n" Expr.Print.meta m Expr.Print.term t)
    u.Unif.t_map

let pp_st fmt st =
  let open Ext_meta in
  List.iter (fun (t, t') -> Format.fprintf fmt "%a == %a\\n" Expr.Print.term t Expr.Print.term t') st.equalities;
  List.iter (fun (t, t') -> Format.fprintf fmt "%a <> %a\\n" Expr.Print.term t Expr.Print.term t') st.inequalities;
  List.iter (fun t -> Format.fprintf fmt "( true) %a\\n" Expr.Print.term t) st.true_preds;
  List.iter (fun t -> Format.fprintf fmt "(false) %a\\n" Expr.Print.term t) st.false_preds

(* Accumulators for constraints *)
(* ************************************************************************ *)

type constraints = (Unif.t, Ext_meta.state, Expr.formula) Constraints.t

type t = {
  id : int;
  acc : constraints;
  level : Solver.level;
}

let make =
  let c = ref 0 in
  (fun acc level -> { id = !c; acc; level; })

(* Builtin symbol *)
(* ************************************************************************ *)

type Expr.builtin += Acc of t

let make_builtin acc =
  let builtin = Acc acc in
  let p = Expr.Id.term_fun ~builtin (Format.sprintf "acc#%d" acc.id) [] [] Expr.Ty.prop in
  Expr.Formula.pred (Expr.Term.apply p [] [])

(* Accumulators *)
(* ************************************************************************ *)

let gen_of_state st =
  let open Ext_meta in
  Gen.(
    append
      (of_list st.inequalities)
      (product (of_list st.true_preds) (of_list st.false_preds))
  )

let unif_depth =
  let refine st =
    let gen = Gen.persistent_lazy @@ gen_of_state st in
    (function s ->
      Gen.Restart.lift (
        Gen.filter_map (fun (t, t') ->
            match Unif.Robinson.term s t t' with
            | x ->
              ignore (Inst.add x);
              Some (x, Expr.Formula.(neg @@ eq t t'))
            | exception Unif.Robinson.Impossible_ty _ -> None
            | exception Unif.Robinson.Impossible_term _ -> None
          )
      ) gen)
  in
  Constraints.make (Gen.singleton Unif.empty) refine

let unif_breadth =
  let gen st = Gen.filter_map (fun (t, t') ->
      let r = Unif.Robinson.find ~section t t' in
      begin match r with Some x -> ignore (Inst.add x) | _ -> () end;
      r) (gen_of_state st) in
  let merger t t' = match Unif.combine t t' with
    | Some s -> Gen.singleton (s, Unif.to_formula t')
    | None -> (fun () -> None)
  in
  Constraints.from_merger gen merger (Gen.singleton Unif.empty)

let empty_cst () =
  match !unif_algo with
  | Unif_depth -> unif_depth
  | Unif_breadth -> unif_breadth

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
        | Some t' -> assert false
      end
    | f -> Ext_meta.parse_aux st f
  in
  let () = iter aux in
  !acc, st


let handle_aux iter acc st =
  Ext_meta.debug_st ~section 30 st;
  let c' = Constraints.add_constraint acc st in
  dump_acc c';
  match Constraints.gen c' () with
  | Some s ->
    let level = Solver.push () in
    Util.debug ~section 10 "New Constraint with subst : %a" Unif.debug s;
    let acc = [make_builtin (make c' level)] in
    let l = Expr.Subst.fold (fun m t acc ->
        [Expr.Formula.eq (Expr.Term.of_meta m) t] :: acc) s.Unif.t_map [] in
    Solver.assume (acc :: l);
    Dispatcher.Ret ()
  | None ->
    Util.debug ~section 2 "Couldn't find a satisfiable constraint";
    if !Ext_meta.meta_start < !Ext_meta.meta_max then begin
      Util.debug ~section 2 "Adding new meta (total: %d)" !Ext_meta.meta_start;
      need_restart := true;
      incr Ext_meta.meta_start;
      Ext_meta.iter Ext_meta.do_formula
    end;
    Dispatcher.(Directive Restart)

let branches_closed = ref 0

let handle : type ret. ret Dispatcher.msg -> ret Dispatcher.result = function
  | Dispatcher.If_sat iter ->
    let cstr, st = match parse iter with
      | None, st ->
        Util.debug ~section 5 "Generating empty constraint";
        let t = empty_cst () in
        dump_new_acc t;
        (t, st)
      | Some t, st ->
        Util.debug ~section 10 "Found previous constraint";
        Solver.pop t.level;
        (t.acc, st)
    in
    begin match handle_aux iter cstr st with
      | Dispatcher.Ret () as ret ->
        incr branches_closed;
        Util.debug ~section 0 "Closed %d branches" !branches_closed;
        ret
      | ret -> ret
    end
  | Solver.Found _ ->
    branches_closed := 0;
    if !need_restart then begin
      need_restart := false;
      Dispatcher.Ret Solver.Ok
    end else
      Dispatcher.Ok
  | _ -> Dispatcher.Ok

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
    Cmdliner.Arg.(value & opt parse_kind Unif_depth & info ["cstr.kind"] ~docv:"METHOD" ~docs ~doc)
  in
  let dot =
    let doc = "Dump a dot graph of the accumulators to the given file" in
    Cmdliner.Arg.(value & opt string "" & info ["cstr.dot"] ~docv:"FILE" ~docs ~doc)
  in
  let aux kind dot =
    unif_algo := kind;
    if not (dot = "") then begin
      let fmt = Format.formatter_of_out_channel (open_out dot) in
      at_exit (fun () ->
          Constraints.dumps pp_unif pp_st Expr.Print.formula fmt !to_dump)
    end
  in
  Cmdliner.Term.(pure aux $ kind $ dot)

;;
Dispatcher.Plugin.register "cstr" ~options
  ~descr:"Handles instanciation using constraints to close multiple branches at the same time"
  (Dispatcher.mk_ext ~section
     ~handle:{Dispatcher.handle=handle}
     ~eval_pred:eval ())
