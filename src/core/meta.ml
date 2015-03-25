
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()
let meta_start = ref 0
let meta_incr = ref false


(* Heuristics *)
type heuristic =
  | No_heuristic
  | Goal_directed

let heuristic_setting = ref No_heuristic

let heur_list = [
  "none", No_heuristic;
  "goal", Goal_directed;
]

let heur_conv = Cmdliner.Arg.enum heur_list

let score u = match !heuristic_setting with
  | No_heuristic -> 0
  | Goal_directed -> Heuristic.goal_directed u

(* Unification options *)
type unif =
  | No_unif
  | Simple
  | ERigid

let unif_setting = ref No_unif

let unif_list = [
  "none", No_unif;
  "simple", Simple;
  "eunif", ERigid;
]

let unif_conv = Cmdliner.Arg.enum unif_list

(* 'Parsing' of formulas *)

type state = {
  mutable true_preds : Expr.term list;
  mutable false_preds : Expr.term list;
  mutable equalities : (Expr.term * Expr.term) list;
  mutable inequalities : (Expr.term * Expr.term) list;
}

let empty_st () = {
  true_preds = [];
  false_preds = [];
  equalities = [];
  inequalities = [];
}

let parse_slice iter =
  let res = empty_st () in
  iter (function
      | { Expr.formula = Expr.Pred p } ->
        res.true_preds <- p :: res.true_preds
      | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred p } } ->
        res.false_preds <- p :: res.false_preds
      | { Expr.formula = Expr.Equal (a, b) } ->
        res.equalities <- (a, b) :: res.equalities
      | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } ->
        res.inequalities <- (a, b) :: res.inequalities
      | _ -> ()
    );
  res

(* Meta variables *)
let metas = H.create 32

let get_nb_metas f =
  try
    H.find metas f
  with Not_found ->
    let i = ref 0 in
    H.add metas f i;
    i

let has_been_seen f = !(get_nb_metas f) > 0

let mark f =
  let i = get_nb_metas f in
  i := !i + 1

(* Proofs *)
let mk_proof_ty f metas = Dispatcher.mk_proof
    ~ty_args:([])
    id "meta"

let mk_proof_term f metas = Dispatcher.mk_proof
    ~term_args:([])
    id "meta"

(* Meta generation & predicates storing *)
let do_formula = function
  | { Expr.formula = Expr.All (l, _, p) } as f ->
    mark f;
    let metas = List.map Expr.term_meta (Expr.new_term_metas f) in
    let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
    let q = Expr.formula_subst Expr.Subst.empty subst p in
    Dispatcher.push [Expr.f_not f; q] (mk_proof_term f metas)
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, p) } } as f ->
    mark f;
    let metas = List.map Expr.term_meta (Expr.new_term_metas f) in
    let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
    let q = Expr.formula_subst Expr.Subst.empty subst p in
    Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_term f metas)
  | { Expr.formula = Expr.AllTy (l, _, p) } as f ->
    mark f;
    let metas = List.map Expr.type_meta (Expr.new_ty_metas f) in
    let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
    let q = Expr.formula_subst subst Expr.Subst.empty p in
    Dispatcher.push [Expr.f_not f; q] (mk_proof_ty f metas)
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, p) } } as f ->
    mark f;
    let metas = List.map Expr.type_meta (Expr.new_ty_metas f) in
    let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
    let q = Expr.formula_subst subst Expr.Subst.empty p in
    Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_ty f metas)
  | _ -> assert false

let do_meta_inst = function
  | { Expr.formula = Expr.All (l, _, p) } as f ->
    mark f;
    let metas = Expr.new_term_metas f in
    let u = List.fold_left (fun s m -> Unif.bind_term s m (Expr.term_meta m)) Unif.empty metas in
    Inst.add u
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, p) } } as f ->
    mark f;
    let metas = Expr.new_term_metas f in
    let u = List.fold_left (fun s m -> Unif.bind_term s m (Expr.term_meta m)) Unif.empty metas in
    Inst.add u
  | { Expr.formula = Expr.AllTy (l, _, p) } as f ->
    mark f;
    let metas = Expr.new_ty_metas f in
    let u = List.fold_left (fun s m -> Unif.bind_ty s m (Expr.type_meta m)) Unif.empty metas in
    Inst.add u
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, p) } } as f ->
    mark f;
    let metas = Expr.new_ty_metas f in
    let u = List.fold_left (fun s m -> Unif.bind_ty s m (Expr.type_meta m)) Unif.empty metas in
    Inst.add u
  | _ -> assert false

(* Assuming function *)
let meta_assume lvl = function
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.ExTy _ } } as f)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.Ex _ } } as f)
  | ({ Expr.formula = Expr.AllTy _ } as f)
  | ({ Expr.formula = Expr.All _ } as f) ->
    if not (has_been_seen f) then for _ = 1 to !meta_start do do_formula f done
  | _ -> ()

(* Unification of predicates *)
let do_inst u = Inst.add ~score:(score u) u

let inst unif p notp =
  let u = unif p notp in
  log 5 "Unification found";
  let l = Inst.split u in
  let l = List.map Inst.simplify l in
  let l = List.map Unif.protect_inst l in
  List.iter do_inst l

let find_inst unif p notp =
  try
    log 5 "Matching : %a ~~ %a" Expr.debug_term p Expr.debug_term notp;
    inst unif p notp;
    inst unif notp p;
    ()
  with
  | Unif.Not_unifiable_ty (a, b) ->
    log 15 "Couldn't unify types %a and %a" Expr.debug_ty a Expr.debug_ty b
  | Unif.Not_unifiable_term (a, b) ->
    log 15 "Couldn't unify terms %a and %a" Expr.debug_term a Expr.debug_term b
  | Rigid.Not_unifiable ->
    log 15 "Unification failed for %a and %a" Expr.debug_term p Expr.debug_term notp

let find_all_insts iter =
  if !meta_incr then
    H.iter (fun f _ -> do_meta_inst f) metas;
  match !unif_setting with
  | No_unif -> ()
  | _ ->
    let st = parse_slice iter in
    let unif = match !unif_setting with
      | No_unif -> assert false
      | Simple -> Unif.cached_unify
      | ERigid ->
        if st.equalities = [] then
          Unif.cached_unify
        else
          Rigid.unify st.equalities
    in
    List.iter (fun p -> List.iter (fun notp  ->
        find_inst unif p notp) st.false_preds) st.true_preds;
    List.iter (fun (a, b) -> find_inst unif a b) st.inequalities

let opts t =
  let docs = Options.ext_sect in
  let inst =
    let doc = Util.sprintf
      "Select unification method to use in order to find instanciations
       $(docv) may be %s." (Cmdliner.Arg.doc_alts_enum ~quoted:false unif_list) in
    Cmdliner.Arg.(value & opt unif_conv No_unif & info ["meta.find"] ~docv:"METHOD" ~docs ~doc)
  in
  let start =
    let doc = "Initial number of metavariables to generate for new formulas" in
    Cmdliner.Arg.(value & opt int 2 & info ["meta.start"] ~docv:"N" ~docs ~doc)
  in
  let incr =
    let doc = "Set the number of new metas to be generated at each pass." in
    Cmdliner.Arg.(value & opt bool false & info ["meta.incr"] ~docs ~doc)
  in
  let heuristic =
    let doc = Util.sprintf
      "Select heuristic to use when assigning scores to possible unifiers/instanciations.
       $(docv) may be %s" (Cmdliner.Arg.doc_alts_enum ~quoted:true heur_list) in
    Cmdliner.Arg.(value & opt heur_conv No_heuristic & info ["meta.heur"] ~docv:"HEUR" ~docs ~doc)
  in
  let set_opts heur start inst incr t =
    heuristic_setting := heur;
    unif_setting := inst;
    meta_start := start;
    meta_incr := incr;
    t
  in
  Cmdliner.Term.(pure set_opts $ heuristic $ start $ inst $ incr $ t)
;;

Dispatcher.(register (
    mk_ext
      ~descr:"Generate meta variables for universally quantified formulas, and use unification to push
              possible instanciations to the 'inst' module."
      ~assume:(fun (f, lvl) -> meta_assume lvl f)
      ~if_sat:find_all_insts
      ~options:opts id "meta"
  ))

