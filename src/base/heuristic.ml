
(* Utilities *)
let nb_metas_in_ty ty =
  let l, l' = Expr.metas_in_ty ty in
  List.length l + List.length l'

let nb_metas_in_term t =
  let l, l' = Expr.metas_in_term t in
  List.length l + List.length l'

(* Goal directed heuristic *)
let goal_meta_mult = 0
let goal_goal_mult = 10

let goal_score_ty ty =
  goal_meta_mult * nb_metas_in_ty ty
  - goal_goal_mult * Expr.(ty.ty_goalness)

let goal_score_term t =
  goal_meta_mult * nb_metas_in_term t
  - goal_goal_mult * Expr.(t.t_goalness)

let goal_directed u =
  Expr.Subst.fold (fun _ t k -> k + goal_score_term t) Unif.(u.t_map)
  (Expr.Subst.fold (fun _ ty k -> k + goal_score_ty ty) Unif.(u.ty_map) 0)

