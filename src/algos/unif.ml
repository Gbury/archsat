(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in literature are
 * actually the meta-variables in the terms *)

(* Occurs check *)
(* ************************************************************************ *)

let rec follow_ty subst = function
  | { Expr.ty = Expr.TyVar v } as t ->
    begin match Mapping.Var.get_ty_opt subst v with
      | Some t' -> follow_ty subst t'
      | None -> t
    end
  | { Expr.ty = Expr.TyMeta m } as t ->
    begin match Mapping.Meta.get_ty_opt subst m with
      | Some t' -> follow_ty subst t'
      | None -> t
    end
  | t -> t

let rec follow_term subst = function
  | { Expr.term = Expr.Var v } as t ->
    begin match Mapping.Var.get_term_opt subst v with
      | Some t' -> follow_term subst t'
      | None -> t
    end
  | { Expr.term = Expr.Meta m } as t ->
    begin match Mapping.Meta.get_term_opt subst m with
      | Some t' -> follow_term subst t'
      | None -> t
    end
  | t -> t

let rec follow_formula subst = function
  | { Expr.formula = Expr.Pred { Expr.term = Expr.Var v } } as f ->
    begin match Mapping.Var.get_formula_opt subst v with
      | Some f' -> follow_formula subst f'
      | None -> f
    end
  | { Expr.formula = Expr.Pred { Expr.term = Expr.Meta m } } as f ->
    begin match Mapping.Meta.get_formula_opt subst m with
      | Some f' -> follow_formula subst f'
      | None -> f
    end
  | f -> f

let rec occurs_ty subst var_l meta_l = function
  | { Expr.ty = Expr.TyVar m' } ->
    CCList.mem ~eq:Expr.Id.equal m' var_l ||
    begin match Mapping.Var.get_ty subst m' with
      | exception Not_found -> false
      | e ->
        let var_l' = CCList.add_nodup ~eq:Expr.Id.equal m' var_l in
        occurs_ty subst var_l' meta_l e
    end
  | { Expr.ty = Expr.TyMeta m' } ->
    CCList.mem ~eq:Expr.Meta.equal m' meta_l ||
    begin match Mapping.Meta.get_ty subst m' with
      | exception Not_found -> false
      | e ->
        let meta_l' = CCList.add_nodup ~eq:Expr.Meta.equal m' meta_l in
        occurs_ty subst var_l meta_l' e
    end
  | { Expr.ty = Expr.TyApp (_, tys) } ->
    List.exists (occurs_ty subst var_l meta_l) tys

let rec occurs_term subst var_l meta_l = function
  | { Expr.term = Expr.Var m' } ->
    CCList.mem ~eq:Expr.Id.equal m' var_l ||
    begin match Mapping.Var.get_term subst m' with
      | exception Not_found -> false
      | e ->
        let var_l' = CCList.add_nodup ~eq:Expr.Id.equal m' var_l in
        occurs_term subst var_l' meta_l e
    end
  | { Expr.term = Expr.Meta m' } ->
    CCList.mem ~eq:Expr.Meta.equal m' meta_l ||
    begin match Mapping.Meta.get_term subst m' with
      | exception Not_found -> false
      | e ->
        let meta_l' = CCList.add_nodup ~eq:Expr.Meta.equal m' meta_l in
        occurs_term subst var_l meta_l' e
    end
  | { Expr.term = Expr.App (_, _, terms) } ->
    List.exists (occurs_term subst var_l meta_l) terms

let occurs_check t =
  Mapping.for_all t
    ~ty_var:(fun v e -> not (occurs_ty t [v] [] e))
    ~ty_meta:(fun m e -> not (occurs_ty t [] [m] e))
    ~term_var:(fun v e -> not (occurs_term t [v] [] e))
    ~term_meta:(fun m e -> not (occurs_term t [] [m] e))

(* Robinson unification *)
(* ************************************************************************ *)

module Robinson = struct

  exception Impossible_ty of Expr.ty * Expr.ty
  exception Impossible_term of Expr.term * Expr.term
  exception Impossible_atomic of Expr.formula * Expr.formula

  let rec ty subst s t =
    let s = follow_ty subst s in
    let t = follow_ty subst t in
    match s, t with
    | ({ Expr.ty = Expr.TyVar v } as m), u
    | u, ({ Expr.ty = Expr.TyVar v } as m) ->
      if Expr.Ty.equal m u then
        subst
      else if occurs_ty subst [v] [] u then
        raise (Impossible_ty (m, u))
      else
        Mapping.Var.bind_ty subst v u
    | ({ Expr.ty = Expr.TyMeta v } as m), u
    | u, ({ Expr.ty = Expr.TyMeta v } as m) ->
      if Expr.Ty.equal m u then
        subst
      else if occurs_ty subst [] [v] u then
        raise (Impossible_ty (m, u))
      else
        Mapping.Meta.bind_ty subst v u
    | { Expr.ty = Expr.TyApp (f, f_args) },
      { Expr.ty = Expr.TyApp (g, g_args) } ->
      if Expr.Id.equal f g then
        List.fold_left2 ty subst f_args g_args
      else
        raise (Impossible_ty (s, t))

  let rec term subst s t =
    let s = follow_term subst s in
    let t = follow_term subst t in
    match s, t with
    | ({ Expr.term = Expr.Var v } as m), u
    | u, ({ Expr.term = Expr.Var v } as m) ->
      if Expr.Term.equal m u then
        subst
      else if occurs_term subst [v] [] u then
        raise (Impossible_term (m, u))
      else
        let subst' = ty subst Expr.(m.t_type) Expr.(u.t_type) in
        Mapping.Var.bind_term subst' v u
    | ({ Expr.term = Expr.Meta v } as m), u
    | u, ({ Expr.term = Expr.Meta v } as m) ->
      if Expr.Term.equal m u then
        subst
      else if occurs_term subst [] [v] u then
        raise (Impossible_term (m, u))
      else
        let subst' = ty subst Expr.(m.t_type) Expr.(u.t_type) in
        Mapping.Meta.bind_term subst' v u
    | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
      { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
      if Expr.Id.equal f g then
        List.fold_left2 term
          (List.fold_left2 ty subst f_ty_args g_ty_args)
          f_t_args g_t_args
      else
        raise (Impossible_term (s, t))

  let term_term subst (a, b) (c, d) =
    try Some (term (term subst a b) c d)
    with Impossible_ty _
       | Impossible_term _ -> None

  let rec atomic subst s t =
    let s = follow_formula subst s in
    let t = follow_formula subst t in
    match s, t with
    | { Expr.formula = Expr.Pred s' },
      { Expr.formula = Expr.Pred t' } ->
      [term subst s' t']
    | { Expr.formula = Expr.Equal (a, b) },
      { Expr.formula = Expr.Equal (c, d) } ->
      CCList.filter_map (fun x -> x) [
        term_term subst (a, c) (d, b);
        term_term subst (a, d) (b, c);
      ]
    | { Expr.formula = Expr.Not s' },
      { Expr.formula = Expr.Not t' } ->
      atomic subst s' t'
    | _ -> raise (Impossible_atomic (s, t))

  let unify_ty ~section f s t =
    Util.enter_prof section;
    match ty Mapping.empty s t with
    | res ->
      Util.exit_prof section;
      f res
    | exception Impossible_ty _ ->
      Util.exit_prof section

  let unify_term ~section f s t =
    Util.enter_prof section;
    match term Mapping.empty s t with
    | res ->
      Util.exit_prof section;
      f res
    | exception Impossible_ty _ ->
      Util.exit_prof section
    | exception Impossible_term _ ->
      Util.exit_prof section

  let find ~section s t =
    Util.enter_prof section;
    let res =
      try Some (term Mapping.empty s t)
      with Impossible_ty _ | Impossible_term _ -> None
    in
    Util.exit_prof section;
    res

end

(* Export unifiers as formulas *)
(* ************************************************************************ *)

let to_formula t =
  Mapping.fold
    ~term_meta:(fun m t f ->
      Expr.(Formula.(f_and [f; eq (Term.of_meta m) t])))
    t Expr.Formula.f_true

(* Caching (modulo meta switching) *)
(* ************************************************************************ *)

module Cache = struct

  exception Impossible_ty of Expr.ty * Expr.ty
  exception Impossible_term of Expr.term * Expr.term

  (* Operations on involutions *)
  let inv_map_ty u m1 m2 =
    try
      let t1 = Mapping.Meta.get_ty u m1 in
      let t2 = Expr.Ty.of_meta m2 in
      if not (Expr.Ty.equal t1 t2) then
        raise (Impossible_ty (t1, t2))
      else
        u
    with Not_found ->
      Mapping.Meta.bind_ty (
        Mapping.Meta.bind_ty u
          m1 (Expr.Ty.of_meta m2)
      ) m2 (Expr.Ty.of_meta m1)

  let inv_map_term u m1 m2 =
    try
      let t1 = Mapping.Meta.get_term u m1 in
      let t2 = Expr.Term.of_meta m2 in
      if not (Expr.Term.equal t1 t2) then
        raise (Impossible_term (t1, t2))
      else
        u
    with Not_found ->
      Mapping.Meta.bind_term (
        Mapping.Meta.bind_term u
          m1 (Expr.Term.of_meta m2)
      ) m2 (Expr.Term.of_meta m1)

  let meta_def m = Expr.Meta.def m.Expr.meta_index
  let meta_ty_def m = Expr.Meta.def m.Expr.meta_index

  (* Finding meta-stable involutions *)
  let rec meta_match_ty subst s t =
    begin match s, t with
      | _, { Expr.ty = Expr.TyVar _ } | { Expr.ty = Expr.TyVar _}, _ -> assert false
      | { Expr.ty = Expr.TyMeta ({ Expr.meta_id = v1 } as m1)},
        { Expr.ty = Expr.TyMeta ({ Expr.meta_id = v2 } as m2)} ->
        if Expr.Id.equal v1 v2 && Expr.Formula.equal (meta_ty_def m1) (meta_ty_def m2) then
          inv_map_ty subst m1 m2
        else
          raise (Impossible_ty (s, t))
      | { Expr.ty = Expr.TyApp (f, f_args) },
        { Expr.ty = Expr.TyApp (g, g_args) } ->
        if Expr.Id.equal f g then
          List.fold_left2 meta_match_ty subst f_args g_args
        else
          raise (Impossible_ty (s, t))
      | _ -> raise (Impossible_ty (s, t))
    end

  let rec meta_match_term subst s t =
    begin match s, t with
      | _, { Expr.term = Expr.Var _ } | { Expr.term = Expr.Var _}, _ -> assert false
      | { Expr.term = Expr.Meta ({ Expr.meta_id = v1 } as m1) },
        { Expr.term = Expr.Meta ({ Expr.meta_id = v2 } as m2)} ->
        if Expr.Id.equal v1 v2 && Expr.Formula.equal (meta_def m1) (meta_def m2) then
          inv_map_term subst m1 m2
        else
          raise (Impossible_term (s, t))
      | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
        { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
        if Expr.Id.equal f g then
          List.fold_left2 meta_match_term
            (List.fold_left2 meta_match_ty subst f_ty_args g_ty_args)
            f_t_args g_t_args
        else
          raise (Impossible_term (s, t))
      | _ -> raise (Impossible_term (s, t))
    end

  module H = Hashtbl.Make(struct
      type t = Expr.term * Expr.term
      let hash (s, t) = Hashtbl.hash (Expr.Term.hash s, Expr.Term.hash t)
      let equal (s1, t1) (s2, t2) =
        try
          let tmp = meta_match_term Mapping.empty s1 s2 in
          let _ = meta_match_term tmp t1 t2 in
          true
        with Impossible_ty _ | Impossible_term _ ->
          false
    end)

  type 'a t = 'a H.t

  let create () = H.create 4096

  let clear = H.clear

  let with_cache cache f a b =
    let key = (a, b) in
    try
      H.find cache key
    with Not_found ->
      let res = f a b in
      H.add cache key res;
      res

end
