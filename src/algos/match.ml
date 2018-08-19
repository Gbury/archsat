(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Matching module *)

(* Matching algorithm *)
(* ************************************************************************ *)

exception Impossible_ty of Expr.ty * Expr.ty
exception Impossible_term of Expr.term * Expr.term
exception Impossible_atomic of Expr.formula * Expr.formula

let rec ty subst pat t =
  match pat, t with
  | { Expr.ty = Expr.TyVar v }, _ ->
    begin match Mapping.Var.get_ty_opt subst v with
      | Some t' ->
        if Expr.Ty.equal t t' then subst
        else raise (Impossible_ty (pat, t))
      | None ->
        Mapping.Var.bind_ty subst v t
    end
  | { Expr.ty = Expr.TyMeta m },
    { Expr.ty = Expr.TyMeta m' } ->
    if Expr.Meta.equal m m' then subst
    else raise (Impossible_ty (pat, t))
  | { Expr.ty = Expr.TyApp (f, f_args) },
    { Expr.ty = Expr.TyApp (g, g_args) } ->
    if Expr.Id.equal f g then
      List.fold_left2 ty subst f_args g_args
    else
      raise (Impossible_ty (pat, t))
  | _ -> raise (Impossible_ty (pat, t))

let rec term subst pat t =
  match pat, t with
  | { Expr.term = Expr.Var v }, _ ->
    begin match Mapping.Var.get_term_opt subst v with
      | Some t' ->
        if Expr.Term.equal t t' then subst
        else raise (Impossible_term (pat, t))
      | None ->
        let subst' = ty subst Expr.(pat.t_type) Expr.(t.t_type) in
        let subst'' = Mapping.Var.bind_term subst' v t in
        subst''
    end
  | { Expr.term = Expr.Meta m },
    { Expr.term = Expr.Meta m' } ->
    if Expr.Meta.equal m m' then subst
    else raise (Impossible_term (pat, t))
  | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
    { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
    if Expr.Id.equal f g then
      List.fold_left2 term
        (List.fold_left2 ty subst f_ty_args g_ty_args)
        f_t_args g_t_args
    else
      raise (Impossible_term (pat, t))
  | _ -> raise (Impossible_term (pat, t))

let rec atomic subst pat a =
  match pat, a with
  | { Expr.formula = Expr.Pred t },
    { Expr.formula = Expr.Pred t' } ->
    term subst t t'
  | { Expr.formula = Expr.Equal (a, b) },
    { Expr.formula = Expr.Equal (c, d) } ->
    begin
      try term (term subst a c) b d
      with
      | Impossible_ty _
      | Impossible_term _ ->
        term (term subst a d) b c
    end
  | { Expr.formula = Expr.Equiv (a, b) },
    { Expr.formula = Expr.Equiv (c, d) } ->
    begin
      try atomic (atomic subst a c) b d
      with
      | Impossible_ty _
      | Impossible_term _
      | Impossible_atomic _ ->
        atomic (atomic subst a d) b c
    end
  | { Expr.formula = Expr.Not pat' },
    { Expr.formula = Expr.Not a' } ->
    atomic subst pat' a'
  | _ -> raise (Impossible_atomic (pat, a))

let find ~section pat t =
  Util.enter_prof section;
  let res =
    try Some (term Mapping.empty pat t)
    with Impossible_ty _ | Impossible_term _ -> None
  in
  Util.exit_prof section;
  res

