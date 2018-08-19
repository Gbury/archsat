(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Dispatcher.section "cstr"

(* Options *)
(* ************************************************************************ *)

let unif_algo = ref `Bad

let kind_list = [
  "close", `Close;
  "unif_d", `Unif_depth;
  (* "unif_b", `Unif_breadth; *)
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

let pp_st fmt st =
  let open Ext_meta in
  List.iter (fun (t, t') -> Format.fprintf fmt "%a == %a\\n" Expr.Print.term t Expr.Print.term t') st.equalities;
  List.iter (fun (t, t') -> Format.fprintf fmt "%a <> %a\\n" Expr.Print.term t Expr.Print.term t') st.inequalities;
  List.iter (fun t -> Format.fprintf fmt "( true) %a\\n" Expr.Print.term t) st.true_preds;
  List.iter (fun t -> Format.fprintf fmt "(false) %a\\n" Expr.Print.term t) st.false_preds

(* Accumulators for constraints *)
(* ************************************************************************ *)

type constraints = (Mapping.t, Ext_meta.state, Expr.formula) Constraints.t

type t = {
  id : int;
  acc : constraints;
  res : Expr.formula list;
}

let make =
  let c = ref 0 in
  (fun acc res -> incr c; { id = !c; acc; res; })

(* Builtin symbol *)
(* ************************************************************************ *)

type Expr.builtin += Acc of t

let make_builtin acc =
  let builtin = Acc acc in
  let p = Expr.Id.term_fun ~builtin
      (Format.sprintf "acc#%d" acc.id) [] [] Expr.Ty.prop in
  let f = Expr.Formula.pred (Expr.Term.apply p [] []) in
  f

(* Accumulators *)
(* ************************************************************************ *)

let gen_of_state st =
  let open Ext_meta in
  Gen.(
    append
      (of_list st.inequalities)
      (product (of_list st.true_preds) (of_list st.false_preds))
  )

let close =
  Constraints.make (Gen.singleton Mapping.empty)
    (fun _ u -> Gen.singleton (u, Expr.Formula.f_true))

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
  Constraints.make (Gen.singleton Mapping.empty) refine

  (*
let unif_breadth =
  let gen st = Gen.filter_map (fun (t, t') ->
      let r = Unif.Robinson.find ~section t t' in
      begin match r with Some x -> ignore (Inst.add x) | _ -> () end;
      r) (gen_of_state st) in
  let merger t t' = match Mapping.merge t t' with
    | Some s -> Gen.singleton (s, Unif.to_formula t')
    | None -> (fun () -> None)
  in
  Constraints.from_merger gen merger (Gen.singleton Unif.empty)
  *)

let empty_cst () =
  match !unif_algo with
  | `Bad -> assert false
  | `Close -> close
  | `Unif_depth -> unif_depth
  (* | `Unif_breadth -> unif_breadth *)

(* Parsing entry formulas *)
(* ************************************************************************ *)

let parse iter =
  let acc = ref None in
  let st = Ext_meta.empty_st () in
  let aux = function
    | { Expr.formula = Expr.Not {
        Expr.formula = Expr.Pred {
            Expr.term = Expr.App ({ Expr.builtin = Acc t }, _, _) } } } ->
      ()
    | { Expr.formula = Expr.Pred {
        Expr.term = Expr.App ({ Expr.builtin = Acc t }, _, _) } } ->
      begin match !acc with
        | None -> acc := Some t
        | Some t' -> assert false
      end
    | f -> Ext_meta.parse_aux st f
  in
  let () = iter aux in
  !acc, st

let handle_aux iter acc old st =
  Util.debug ~section "state:@ @[<hov>%a@]" Ext_meta.print st;
  let c = Constraints.add_constraint acc st in
  dump_acc c;
  match Constraints.gen c () with
  | Some s ->
    Util.debug ~section "New Constraint with subst : %a" Mapping.print s;
    (* Old behavior, quite certainly incomplete. *)
    (*
    let accs, acc = make_builtin (make c') in
    let l = Expr.Subst.fold (fun m t acc ->
        Expr.Formula.eq (Expr.Term.of_meta m) t :: acc) s.Unif.t_map [] in
    Solver.Assume (acc :: l @ (List.map Expr.Formula.neg accs))
    *)
    (* New behavior, close the current branch. *)
    let new_f = Expr.Formula.neg (Expr.Formula.f_and st.Ext_meta.formulas) in
    let l = new_f :: old in
    let pred = make_builtin (make c l) in
    Solver.Assume (pred :: l)
  | None ->
    Util.debug ~section "Couldn't find a satisfiable constraint";
    if !Ext_meta.meta_start < !Ext_meta.meta_max then begin
      Util.debug ~section "Adding new meta (total: %d)" !Ext_meta.meta_start;
      incr Ext_meta.meta_start;
      Ext_meta.iter Ext_meta.do_formula;
      Solver.Restart
    end else
      Solver.Sat_ok

let branches_closed = ref 0

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Solver.Restarting ->
    branches_closed := 0;
    Some ()
  | Solver.Found_sat iter ->
    let cstr, old, st = match parse iter with
      | None, st ->
        Util.info ~section "Generating empty constraint";
        let t = empty_cst () in
        dump_new_acc t;
        (t, [], st)
      | Some t, st ->
        Util.info ~section "Found previous constraint";
        (t.acc, t.res, st)
    in
    let ret = handle_aux iter cstr old st in
    begin match ret with
      | Solver.Assume _ ->
        incr branches_closed;
        Util.debug ~section "Closed %d branches" !branches_closed
      | _ -> ()
    end;
    Some ret
  | _ -> None

(* Evaluating *)
(* ************************************************************************ *)

let options =
  let docs = Options.ext_sect in
  let kind =
    let doc = Format.asprintf "The constraint generation method to use,
    $(docv) may be %s" (Cmdliner.Arg.doc_alts_enum ~quoted:false kind_list) in
    Cmdliner.Arg.(value & opt parse_kind `Close & info ["cstr.kind"] ~docv:"METHOD" ~docs ~doc)
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
          Constraints.dumps Mapping.print pp_st Expr.Print.formula fmt !to_dump)
    end
  in
  Cmdliner.Term.(pure aux $ kind $ dot)

let register () =
  Dispatcher.Plugin.register "cstr" ~options
    ~descr:"Handles instanciation using constraints to close multiple branches at the same time"
    (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle=handle} ())

