
(* Option helpers *)
let opt = function Some x -> x | None -> assert false

(* Instanciation helpers *)
let index m = Expr.(m.meta_index)
let meta_def m = Expr.get_meta_def (index m)
let meta_ty_def m = Expr.get_meta_ty_def (index m)

(* Partial order, representing the inclusion on quantified formulas
 * Uses the free variables to determine inclusion. *)
let free_args = function
  | { Expr.formula = Expr.All (_, args, _) }
  | { Expr.formula = Expr.Ex (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, args, _) } }
  | { Expr.formula = Expr.AllTy (_, args, _) }
  | { Expr.formula = Expr.ExTy (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (_, args, _) } } -> args
  | _ -> assert false

let sub_quant p q = match p with
  | { Expr.formula = Expr.All (l, _, _) }
  | { Expr.formula = Expr.Ex (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, _) } } ->
    let _, tl = free_args q in
    List.exists (fun t -> List.exists (Expr.Term.equal t) tl) (List.map Expr.term_var l)
  | { Expr.formula = Expr.AllTy (l, _, _) }
  | { Expr.formula = Expr.ExTy (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, _) } } ->
    let tyl, _ = free_args q in
    List.exists (fun ty -> List.exists (Expr.Ty.equal ty) tyl) (List.map Expr.type_var l)
  | _ -> assert false

let quant_compare p q =
  if Expr.Formula.equal p q then
      Some 0
  else if sub_quant p q then
      Some 1
  else if sub_quant q p then
      Some ~-1
  else
      None

let quant_comparable p q = match quant_compare p q with
  | Some _ -> true
  | None -> false

(* Splits an arbitrary unifier (Unif.t) into a list of
 * unifiers such that all formula generating the metas in
 * a unifier are comparable according to compare_quant. *)
let belong_ty m s =
    let p = Expr.get_meta_ty_def (index m) in
    let aux m' _ = quant_comparable p (Expr.get_meta_ty_def (index m')) in
    Expr.Subst.exists aux Unif.(s.ty_map)

let belong_term m s =
    let p = Expr.get_meta_def (index m) in
    let aux m' _ = quant_comparable p (Expr.get_meta_def (index m')) in
    Expr.Subst.exists aux Unif.(s.t_map)

let split s =
  let rec aux bind belongs acc m t = function
      | [] -> bind Unif.empty m t :: acc
      | s :: r ->
        if belongs m s then
          (bind s m t) :: (List.rev_append acc r)
        else
          aux bind belongs (s :: acc) m t r
  in
  Expr.Subst.fold (aux Unif.bind_term belong_term []) Unif.(s.t_map)
    (Expr.Subst.fold (aux Unif.bind_ty belong_ty []) Unif.(s.ty_map) [])

(* Given a unifier such that all formula generating metas in it are comparable
 * (according to compare_quant), returns a unifiers that maps all variables
 * of the generating formulas. *)
let add_meta_ty subst = function
  | { Expr.ty = Expr.TyMeta m } as t -> if Unif.mem_ty subst m then subst else Unif.bind_ty subst m t
  | _ -> subst
let add_meta_term subst = function
  | { Expr.term = Expr.Meta m } as t -> if Unif.mem_term subst m then subst else Unif.bind_term subst m t
  | _ -> subst

let complete_ty_aux m _ s =
    let l, l' = free_args (Expr.get_meta_def (index m)) in
    assert (l' = []);
    let s' = List.fold_left add_meta_ty s l in
    List.fold_left add_meta_ty s' (List.map Expr.type_meta (Expr.ty_metas_of_index (index m)))

let complete_term_aux m _ s =
    let l, l' = free_args (Expr.get_meta_def (index m)) in
    let s' = List.fold_left add_meta_ty s l in
    let s'' = List.fold_left add_meta_term s l' in
    List.fold_left add_meta_term s' (List.map Expr.term_meta (Expr.term_metas_of_index (index m)))

let complete_ty s = Expr.Subst.fold complete_ty_aux Unif.(s.ty_map) s
let complete_term s = Expr.Subst.fold complete_term_aux Unif.(s.t_map) s

let complete s = complete_term (complete_ty s)

(* Given an arbitrary substitution (Unif.t),
 * Returns a list of (meta_index * Unif.t) that
 * aggregates metas with the same index. *)
let partition s =
    let rec aux f bind acc m t = function
        | [] -> (f, bind Unif.empty m t) :: acc
        | (f', s) :: r when Expr.Formula.equal f' f->
          (f', bind s m t) :: (List.rev_append acc r)
        | x :: r -> aux f bind (x :: acc) m t r
    in
    Expr.Subst.fold (fun m t acc -> aux (meta_def m) Unif.bind_term [] m t acc) Unif.(s.t_map) (
        Expr.Subst.fold (fun m t acc -> aux (meta_ty_def m) Unif.bind_ty []m t acc) Unif.(s.ty_map) [])

(* Ordering of the formulas for instanciation (biggest first)
 * We suppose that all formulas in the list are comparable according to compare_quant. *)
let inst_order = List.sort (fun (f, _) (f', _) -> opt (quant_compare f' f))

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof id f p s = Dispatcher.mk_proof
    ~ty_args:(Expr.Subst.fold (fun m t l -> Expr.type_meta m :: t :: l) Unif.(s.ty_map) [])
    ~term_args:(Expr.Subst.fold (fun m t l -> Expr.term_meta m :: t :: l) Unif.(s.t_map) [])
    ~formula_args:[f; p] id "inst"

(* Applies substitutions in order to provide a coherent
 * instanciation scheme. Returns a triplet
 * (formula list) * proof, representing the instanciations
 * to do, together with their proof *)
let apply_subst s f =
    let aux m t s =
        Expr.Subst.Var.bind Expr.(m.meta_var) t s
    in
    Expr.formula_subst
        (Expr.Subst.fold aux Unif.(s.ty_map) Expr.Subst.empty)
        (Expr.Subst.fold aux Unif.(s.t_map) Expr.Subst.empty)
        f

let rec fold_subst id subst = function
    | [] -> []
    | (f, s) :: r ->
      let f' = apply_subst subst f in
      match f' with
      | { Expr.formula = Expr.All (_, _, p) } | { Expr.formula = Expr.AllTy (_, _, p) } ->
        let q = apply_subst s p in
        let res = [ Expr.f_not f'; q], mk_proof id f' q s in
        res :: (fold_subst id (Unif.merge subst s) r)
      | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, _, p) } }
      | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (_, _, p) } } ->
        let q = apply_subst s (Expr.f_not p) in
        let res = [ Expr.f_not f'; q], mk_proof id f' q s in
        res :: (fold_subst id (Unif.merge subst s) r)
      | _ -> assert false

(* Dispatcher extension part *)
let id = Dispatcher.new_id ()

let instanciation s =
  let l = partition s in
  let l = inst_order l in
  let l = fold_subst id Unif.empty l in
  List.iter (fun (cl, p) -> Dispatcher.push cl p) l

;;
Dispatcher.(register {
    id = id;
    name = "inst";
    assume = (fun _ -> ());
    eval_pred = (fun _ -> None);
    preprocess = (fun _ -> ());
    if_sat = (fun _ -> ());
    })
