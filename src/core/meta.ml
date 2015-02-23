
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)
module S = Backtrack.HashtblBack(Expr.Term)
module U = Hashtbl.Make(Unif)

let id = Dispatcher.new_id ()
let no_inst = ref false
let incr = ref 1

(* Hashtbl to store number of generated metas for each formula *)
let metas = H.create 256

let get_nb_metas f = try H.find metas f with Not_found -> 0

let has_been_seen f = get_nb_metas f > 0

let mark f = H.add metas f (get_nb_metas f + 1)

(* Small helper *)
(* TODO *)
let mk_proof_ty f metas = Dispatcher.mk_proof
  ~ty_args:([])
  id "meta"

let mk_proof_term f metas = Dispatcher.mk_proof
  ~term_args:([])
  id "meta"

(* Set of predicates to unify *)
let unif_set = U.create 256
let true_preds = S.create Dispatcher.stack
let false_preds = S.create Dispatcher.stack

let mem x tbl = S.mem tbl x

let print_inst s =
    Expr.Subst.iter (fun k v -> log 5 " |- %a -> %a" Expr.debug_meta k Expr.debug_term v) Unif.(s.t_map)

let do_unif u =
  if not (U.mem unif_set u) then begin
    U.add unif_set u 0;
    log 10 "Found inst";
    print_inst u;
    if not !no_inst then begin
      let l = Inst.instanciation id u in
      List.iter (fun (cl, proof) -> Dispatcher.push cl proof) l
    end
  end else
    let i = U.find unif_set u in
    U.add unif_set u (i + 1)

let inst p notp =
  let unif = Unif.cached_unify p notp in
  log 5 "Unification found";
  let l = List.map Unif.complete (Unif.split unif) in
  List.iter do_unif l

let find_inst p notp =
    try
        log 5 "Matching : %a ~~ %a" Expr.debug_term p Expr.debug_term notp;
        inst p notp;
        inst notp p
    with
    | Unif.Not_unifiable_ty (a, b) ->
        log 15 "Couldn't unify types %a and %a" Expr.debug_ty a Expr.debug_ty b
    | Unif.Not_unifiable_term (a, b) ->
        log 15 "Couldn't unify terms %a and %a" Expr.debug_term a Expr.debug_term b

let do_formula = function
    | { Expr.formula = Expr.All (l, _, p) } as f ->
      mark f; (* Do not re-generate metas *)
      let metas = List.map Expr.term_meta (Expr.new_term_metas f) in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof_term f metas)
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, p) } } as f ->
      mark f; (* Do not re-generate metas *)
      let metas = List.map Expr.term_meta (Expr.new_term_metas f) in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_term f metas)
    | { Expr.formula = Expr.AllTy (l, _, p) } as f ->
      mark f; (* Do not re-generate metas *)
      let metas = List.map Expr.type_meta (Expr.new_ty_metas f) in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l metas in
      let q = Expr.formula_subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof_ty f metas)
    | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, p) } } as f ->
      mark f; (* Do not re-generate metas *)
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
    for i = 1 to !incr do
        H.iter (fun f _ -> do_formula f) metas
    done

let meta_eval _ = None

let meta_pre _ = ()
;;


Dispatcher.register_options [
    "-no-inst", Arg.Set no_inst,
    " Do no instanciations other than metavariables (for universally quantified formulas)";
    "-meta-incr", Arg.Int (fun i -> incr := i),
    " Set the number of new metas to be generated at eash pass (default = 1)";
]
;;
Dispatcher.(register {
    id = id;
    name = "meta";
    assume = (fun (f, lvl) -> meta_assume lvl f);
    eval_pred = meta_eval;
    preprocess = meta_pre;
    if_sat = find_all_insts;
  })

