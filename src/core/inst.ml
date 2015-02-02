
(* Instanciation helpers *)
let index m = Expr.(m.meta_index)

let rec aggregate acc = function
    | [] -> acc
    | ((m, _) as h) :: r -> begin match acc with
      | ( ( (m', _) :: _ ) as head ) :: tail when (index m) = (index m') ->
        aggregate ((h :: head) :: tail) r
      | _ -> aggregate ([h] :: acc) r
    end

(* Given an arbitrary list (meta, term),
 * Returns a list of lists (meta, term) that
 * aggregates metas with the same index. *)
let partition l =
    let l = List.sort (fun (m, _) (m', _) -> compare (index m) (index m')) l in
    aggregate [] l

(* Takes a substitution (meta, term) and returns a triplet
 * formula * lvl * (meta, term) list. *)
let formula_subst subst =
    assert (subst <> []);
    let m = fst (List.hd subst) in
    let f = Expr.get_meta_def (index m) in
    f, Expr.(m.meta_level), subst

(* Ordering on the meta-creation level of the formulas *)
let inst_order (_, i, _) (_, j, _) = compare j i

(* Applies substitutions in order to provide a coherent
 * instanciation scheme. Returns a triplet
 * formula * term list * formula, such that
 * the right formula is the result of instanciating the left one. *)
let var_subst_of_list = List.fold_left (fun s (v, t) -> Expr.Subst.bind v t s) Expr.Subst.empty

let make_inst vars l =
    let rec aux l subst acc = function
        | [] -> subst, List.rev acc
        | v :: r ->
          begin try
            let (m, t) = List.find (fun (m, _) ->
                Expr.(m.meta_var.var_name = v.var_name)) l
            in
            aux l ((v, t) :: subst) acc r
          with Not_found ->
            aux l subst (v :: acc) r
          end
    in
    aux l [] [] vars

let apply_subst (f, _, l) =
      let s, p = match f with
      | { Expr.formula = Expr.All (vars, p) } ->
        let var_subst, new_vars = make_inst vars l in
        let f' = Expr.f_all new_vars p in
        var_subst, Expr.formula_subst Expr.Subst.empty (var_subst_of_list var_subst) f'
      | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex(vars, p) } } ->
        let var_subst, new_vars = make_inst vars l in
        let f' = Expr.f_not (Expr.f_ex new_vars p) in
        var_subst, Expr.formula_subst Expr.Subst.empty (var_subst_of_list var_subst) f'
      | _ -> assert false
      in
      (f, s, p)

(* Takes ... *)
let add_proof id (f, l, p) =
    let l' = Util.list_flatmap (fun (v, t) -> [Expr.term_var v; t]) l in
    ([Expr.f_not f; p], (id, "inst", [f; p], l'))

let instanciation id l =
  assert (l <> []);
  let l = partition l in
  let l = List.map formula_subst l in
  let l = List.sort inst_order l in
  let p = apply_subst (List.hd l) in
  add_proof id p

