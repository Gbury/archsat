(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Heuristic parameters *)
(* ************************************************************************ *)

let goal_size_mult = 0
let goal_meta_mult = 0
let goal_goal_mult = ~- 100

(* Utilities *)
(* ************************************************************************ *)

let nb_metas_in_ty ty =
  let l, l' = Expr.Ty.fm ty in
  List.length l + List.length l'

let nb_metas_in_term t =
  let l, l' = Expr.Term.fm t in
  List.length l + List.length l'

let rec ty_size = function
  | { Expr.ty = Expr.TyApp (f, args) } ->
    1 + List.fold_left (fun acc ty -> max acc (ty_size ty)) 0 args
  | _ -> 0

let rec term_size = function
  | { Expr.term = Expr.App (f, _, args) } ->
    1 + List.fold_left (fun acc ty -> max acc (term_size ty)) 0 args
  | _ -> 0

(* Does the type/term include goal-oriented subterms ? *)
(* ************************************************************************ *)

let rec has_goal_subty = function
  | ty when ty.Expr.ty_status = Expr.Status.goal ->
    true
  | { Expr.ty = Expr.TyApp (_, l); _ } ->
    List.exists has_goal_subty l
  | _ -> false

let rec has_goal_subterm = function
  | t when t.Expr.t_status = Expr.Status.goal ->
    true
  | { Expr.term = Expr.App (_, _, l); _ } ->
    List.exists has_goal_subterm l
  | _ -> false

(* Goal directed heuristic *)
(* ************************************************************************ *)

let goal_score_ty ty =
  let goal = if has_goal_subty ty then 1 else 0 in
  goal_size_mult * ty_size ty
  + goal_meta_mult * nb_metas_in_ty ty
  + goal_goal_mult * goal

let goal_score_term t =
  let goal = if has_goal_subterm t then 1 else 0 in
  goal_size_mult * term_size t
  + goal_meta_mult * nb_metas_in_term t
  + goal_goal_mult * goal

let goal_directed u =
  let aux_t _ t (h, k) = (h + goal_score_term t, k + 1) in
  let aux_ty _ ty (h, k) = (h + goal_score_ty ty, k + 1) in
  let tot, n =
    Mapping.fold
      ~ty_var:aux_ty ~ty_meta:aux_ty
      ~term_var:aux_t ~term_meta:aux_t
      u (0,0)
  in
  tot / n

