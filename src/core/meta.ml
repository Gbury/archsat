
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)
module S = Backtrack.HashtblBack(Expr.Term)

let id = Dispatcher.new_id ()
let no_inst = ref false
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

(* Hashtbl to store number of generated metas for each formula *)
let metas = H.create 256

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

(* Set of predicates to unify *)
let true_preds = S.create ~size:4096 Dispatcher.stack
let false_preds = S.create ~size:4096 Dispatcher.stack

let mem x tbl = S.mem tbl x

(* Unification of predicates *)
let do_inst u = Inst.add ~score:(score u) u

let inst p notp =
  let unif = Unif.cached_unify p notp in
  log 5 "Unification found";
  Expr.Subst.iter (fun k v -> log 5 " |- %a -> %a"
                      Expr.debug_meta k Expr.debug_term v) Unif.(unif.t_map);
  let l = Inst.split unif in
  let l = List.map Inst.simplify l in
  let l = List.map Unif.protect_inst l in
  List.iter do_inst l

let find_inst p notp =
  try
    log 5 "Matching : %a ~~ %a" Expr.debug_term p Expr.debug_term notp;
    inst p notp;
    inst notp p;
    ()
  with
  | Unif.Not_unifiable_ty (a, b) ->
    log 15 "Couldn't unify types %a and %a" Expr.debug_ty a Expr.debug_ty b
  | Unif.Not_unifiable_term (a, b) ->
    log 15 "Couldn't unify terms %a and %a" Expr.debug_term a Expr.debug_term b

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
  (* Term metas generation *)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, p) } } as f)
  | ({ Expr.formula = Expr.All (l, _, p) } as f) ->
    if not (has_been_seen f) then for _ = 1 to !meta_start do do_formula f done
  (* Unification discovery *)
  | { Expr.formula = Expr.Pred p } ->
    if not (mem p true_preds) then begin
      S.add true_preds p lvl
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred p } } ->
    if not (mem p false_preds) then begin
      S.add false_preds p lvl
    end
  | _ -> ()

let find_all_insts () =
  S.iter (fun p _ -> S.iter (fun notp _ -> find_inst p notp) false_preds) true_preds;
  if !meta_incr then
    H.iter (fun f _ -> do_meta_inst f) metas

let opts t =
  let docs = Options.ext_sect in
  let inst =
    let doc = "Decide wether metavariables are to be instanciated." in
    Cmdliner.Arg.(value & opt bool true & info ["meta.inst"] ~docv:"BOOL" ~docs ~doc)
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
    no_inst := not inst;
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

