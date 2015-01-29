
(* Instanciation helpers *)
let index m = Expr.(m.meta_index)

let rec aggregate acc = function
    | [] -> acc
    | ((m, _) as h) :: r -> begin match acc with
      | ( ( (m', _) :: _ ) as head ) :: tail when (index m) = (index m') ->
        aggregate ((h :: head) :: tail) r
      | _ -> aggregate ([h] :: acc) r
    end

let compare_meta_pair (m, _) (m', _) = compare (index m) (index m')

let eq_meta_pair p p' = compare_meta_pair p p' = 0

(* Given an arbitrary list (meta, term),
 * Returns a list of lists (meta, term) that
 * aggregates metas with the same index. *)
let partition l =
    let l = List.sort compare_meta_pair l in
    aggregate [] l

(* Takes a list (meta, term) with metas at the same index,
 * and returns a list (meta, term) so that it forms a
 * complete substitution for the generating formula. *)
let meta_completion l =
  assert (l <> []);
  let (m, _) = List.hd l in
  let subst = Expr.other_term_metas m in
  let aux (m, t) = try List.find (eq_meta_pair (m, t)) l with Not_found -> (m, t) in
  List.map aux subst

(* Takes a substitution (meta, term) and returns a triplet
 * formula * lvl * (var, meta, term) list. *)
let formula_subst subst =
    assert (subst <> []);
    let m = fst (List.hd subst) in
    let f = Expr.get_meta_def (index m) in
    match f with
    | { Expr.formula = Expr.All (l, _) }
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex(l, _) } } ->
      f, Expr.(m.meta_level), (List.map2 (fun v (m, t) -> (v, m, t)) l subst)
    | _ -> assert false

(* Ordering on the meta-creation level of the formulas *)
let inst_order (_, i, _) (_, j, _) = compare j i

(* Applies substitutions in order to provide a coherent
 * instanciation scheme. Returns a triplet
 * formula * term list * formula, such that
 * the right formula is the result of instanciating the left one. *)
let var_subst_of_list = List.fold_left (fun s (v, _, t) -> Expr.Subst.bind v t s) Expr.Subst.empty

let add_meta_subst = List.fold_left (fun s (_, m, t) -> Expr.Subst.bind Expr.(m.meta_var) t s)

let rec apply_substs meta_subst = function
    | [] -> []
    | (f, _, l) :: r ->
      let f = Expr.formula_subst Expr.Subst.empty meta_subst f in
      let p = match f with
      | { Expr.formula = Expr.All (_, p) } ->
        Expr.formula_subst Expr.Subst.empty (var_subst_of_list l) p
      | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex(_, p) } } ->
        Expr.f_not (Expr.formula_subst Expr.Subst.empty (var_subst_of_list l) p)
      | _ -> assert false
      in
      (f, (List.map (fun (_, _, t) -> t) l), p) ::
          (apply_substs (add_meta_subst meta_subst l) r)

(* Takes ... *)
let add_proof id (f, l, p) = ([Expr.f_not f; p], (id, "inst", [f; p], l))

let instanciations id l =
  let l = partition l in
  let l = List.map meta_completion l in
  let l = List.map formula_subst l in
  let l = List.sort inst_order l in
  let l = apply_substs Expr.Subst.empty l in
  List.map (add_proof id) l

