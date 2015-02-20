
(* Instanciation helpers *)
let index m = Expr.(m.meta_index)
let meta_def m = Expr.get_meta_def (index m)
let meta_ty_def m = Expr.get_meta_ty_def (index m)

(* Given an arbitrary substitution (Unif.t),
 * Returns a list of (int * Unif.t) that
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
 * Here, we use the free variables of quantifiers to determine
 * the subterm relation on quantified formulas *)
let open_ty_meta = function
    | { Expr.ty = Expr.TyMeta { Expr.meta_var = v } } -> v
    | _ -> assert false
let open_meta = function
    | { Expr.term = Expr.Meta { Expr.meta_var = v } } -> v
    | _ -> assert false

let free_vars = function
  | { Expr.formula = Expr.All (_, args, _) }
  | { Expr.formula = Expr.Ex (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, args, _) } } ->
    let l, l' = args in
    List.map open_ty_meta l, List.map open_meta l'
  | _ -> assert false

let sub_quant p q = match p with
  | { Expr.formula = Expr.All (l, _, _) }
  | { Expr.formula = Expr.Ex (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, _) } } ->
    let _, tl = free_vars q in
    List.exists (fun v -> List.exists (Expr.Var.equal v) tl) l
  | { Expr.formula = Expr.AllTy (l, _, _) }
  | { Expr.formula = Expr.ExTy (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, _) } } ->
    let tyl, _ = free_vars q in
    List.exists (fun v -> List.exists (Expr.Var.equal v) tyl) l
  | _ -> assert false

let quant_compare p q =
  if Expr.Formula.equal p q then
      0
  else if sub_quant p q then
      1
  else if sub_quant q p then
      -1
  else
      assert false

let inst_order = List.sort (fun (f, _) (f', _) -> quant_compare f' f)

(* Takes ... *)
let mk_proof id f p s = Dispatcher.({
    proof_ext = id;
    proof_name = "inst";
    proof_ty_args = Expr.Subst.fold (fun m t l -> Expr.type_meta m :: t :: l) Unif.(s.ty_map) [];
    proof_term_args = Expr.Subst.fold (fun m t l -> Expr.term_meta m :: t :: l) Unif.(s.t_map) [];
    proof_formula_args = [f; p];
})

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

let add_subst subst s =
    Expr.Subst.fold Expr.Subst.Var.bind subst s

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

let instanciation id s =
  let l = partition s in
  let l = inst_order l in
  fold_subst id Unif.empty l

