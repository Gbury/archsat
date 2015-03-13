
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)
module S = Backtrack.HashtblBack(Expr.Term)

let id = Dispatcher.new_id ()
let no_inst = ref false
let meta_incr = ref 0

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

(* Small helper *)
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
let do_inst u = Inst.add u

let inst p notp =
  let unif = Unif.unify_term p notp in
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

(* Assuming function *)
let meta_assume lvl = function
  (* Term metas generation *)
  | { Expr.formula = Expr.All (l, _, p) } as f ->
    if not (has_been_seen f) then do_formula f
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, p) } } as f ->
    if not (has_been_seen f) then do_formula f
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
  for _ = 1 to !meta_incr do
    H.iter (fun f _ -> do_formula f) metas
  done

let opts t =
  let docs = Options.ext_sect in
  let inst =
    let doc = "Decide wether metavariables are to be instanciated." in
    Cmdliner.Arg.(value & opt bool true & info ["meta.inst"] ~docv:"BOOL" ~docs ~doc)
  in
  let incr =
    let doc = "Set the number of new metas to be generated at each pass." in
    Cmdliner.Arg.(value & opt int 0 & info ["meta.incr"] ~docv:"INT" ~docs ~doc)
  in
  let set_opts inst incr t =
    no_inst := not inst;
    meta_incr := incr;
    t
  in
  Cmdliner.Term.(pure set_opts $ inst $ incr $ t)
;;

Dispatcher.(register (
    mk_ext
      ~descr:"Generate meta variables for universally quantified formulas, and use unification to push
              possible instanciations to the 'inst' module."
      ~assume:(fun (f, lvl) -> meta_assume lvl f)
      ~if_sat:find_all_insts
      ~options:opts id "meta"
  ))

