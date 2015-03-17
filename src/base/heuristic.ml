
(* Heuristic parameters *)
(* ************************************************************************ *)

let goal_meta_mult = 0
let goal_goal_mult = 100

(* Utilities *)
(* ************************************************************************ *)

let nb_metas_in_ty ty =
  let l, l' = Expr.metas_in_ty ty in
  List.length l + List.length l'

let nb_metas_in_term t =
  let l, l' = Expr.metas_in_term t in
  List.length l + List.length l'

(* Goal directed heuristic *)
(* ************************************************************************ *)

let goal_score_ty ty =
  goal_meta_mult * nb_metas_in_ty ty
  - goal_goal_mult * Expr.(ty.ty_goalness)

let goal_score_term t =
  goal_meta_mult * nb_metas_in_term t
  - goal_goal_mult * Expr.(t.t_goalness)

let goal_directed u =
  let tot, n = Expr.Subst.fold (fun _ t (h, k) -> (h + goal_score_term t, k + 1)) Unif.(u.t_map)
            (Expr.Subst.fold (fun _ ty (h, k) -> (h + goal_score_ty ty, k + 1)) Unif.(u.ty_map) (0,0)) in
  tot / n

