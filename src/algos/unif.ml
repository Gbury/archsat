
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

(* Unifiers *)
(* ************************************************************************ *)

(* Definition *)
type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}

let empty = {
  ty_map = Expr.Subst.empty;
  t_map = Expr.Subst.empty;
}

let is_empty u =
  Expr.Subst.is_empty u.ty_map &&
  Expr.Subst.is_empty u.t_map

let mem_ty subst m = Expr.Subst.Meta.mem m subst.ty_map
let mem_term subst m = Expr.Subst.Meta.mem m subst.t_map

let get_ty subst m = Expr.Subst.Meta.get m subst.ty_map
let get_term subst m = Expr.Subst.Meta.get m subst.t_map

let get_ty_opt subst m =
  try Some (Expr.Subst.Meta.get m subst.ty_map)
  with Not_found -> None

let get_term_opt subst m =
  try Some (Expr.Subst.Meta.get m subst.t_map)
  with Not_found -> None

let bind_ty subst m t = { subst with ty_map = Expr.Subst.Meta.bind subst.ty_map m t }
let bind_term subst m t = { subst with t_map = Expr.Subst.Meta.bind subst.t_map m t }

let hash s =
  Hashtbl.hash (Expr.Subst.hash Expr.Ty.hash s.ty_map, Expr.Subst.hash Expr.Term.hash s.t_map)

let compare s u =
  match Expr.Subst.compare Expr.Ty.compare s.ty_map u.ty_map with
  | 0 -> Expr.Subst.compare Expr.Term.compare s.t_map u.t_map
  | x -> x

let equal s u =
  Expr.Subst.equal Expr.Ty.equal s.ty_map u.ty_map &&
  Expr.Subst.equal Expr.Term.equal s.t_map u.t_map

let print fmt s =
  Format.fprintf fmt "@<hov 1>{%a;@ %a}@]"
    (Expr.Subst.print Expr.Print.meta Expr.Print.ty) s.ty_map
    (Expr.Subst.print Expr.Print.meta Expr.Print.term) s.t_map

let inverse s =
  Expr.Subst.fold (fun m t s ->
      match t with
      | { Expr.term = Expr.Meta m' } -> bind_term s m' (Expr.Term.of_meta m)
      | _ -> bind_term s m t
    ) s.t_map (Expr.Subst.fold (fun m ty s ->
      match ty with
      | { Expr.ty = Expr.TyMeta m' } -> bind_ty s m' (Expr.Ty.of_meta m)
      | _ -> bind_ty s m ty
    ) s.ty_map empty)

(* Occurs check *)
(* ************************************************************************ *)

let rec follow_ty subst = function
  | { Expr.ty = Expr.TyMeta m } as t ->
    begin match get_ty_opt subst m with
      | Some t' -> follow_ty subst t'
      | None -> t
    end
  | t -> t

let rec follow_term subst = function
  | { Expr.term = Expr.Meta m } as t ->
    begin match get_term_opt subst m with
      | Some t' -> follow_term subst t'
      | None -> t
    end
  | t -> t

let rec occurs_ty subst l = function
  | { Expr.ty = Expr.TyMeta m' } ->
    List.exists (Expr.Meta.equal m') l ||
    begin match get_ty subst m' with
      | exception Not_found -> false
      | e -> occurs_ty subst (m' :: l) e
    end
  | { Expr.ty = Expr.TyApp (_, tys) } ->
    List.exists (occurs_ty subst l) tys
  | _ -> false

let rec occurs_term subst l = function
  | { Expr.term = Expr.Meta m' } ->
    List.exists (Expr.Meta.equal m') l ||
    begin match get_term subst m' with
      | exception Not_found -> false
      | e -> occurs_term subst (m' :: l) e
    end
  | { Expr.term = Expr.App (_, _, terms) } ->
    List.exists (occurs_term subst l) terms
  | _ -> false

let occurs_check t =
  Expr.Subst.for_all (fun v e -> not (occurs_ty t [v] e)) t.ty_map &&
  Expr.Subst.for_all (fun v e -> not (occurs_term t [v] e)) t.t_map

(* Manipulation over meta substitutions *)
(* ************************************************************************ *)

(* Substitutes meta instead of variables *)
let rec type_subst_aux u = function
  | { Expr.ty = Expr.TyVar _ } as t -> t
  | { Expr.ty = Expr.TyMeta m } as t ->
    begin match Expr.Subst.Meta.get m u.ty_map with
    | exception Not_found -> t
    | t' -> type_subst_aux u t'
    end
  | { Expr.ty = Expr.TyApp (f, args) } as ty ->
    let new_args = List.map (type_subst_aux u) args in
    if List.for_all2 (==) args new_args then ty
    else Expr.Ty.apply f new_args

let type_subst u t = if Expr.Subst.is_empty u.ty_map then t else type_subst_aux u t

let rec term_subst_aux u = function
  | { Expr.term = Expr.Var _ } as t -> t
  | { Expr.term = Expr.Meta m } as t ->
    begin match Expr.Subst.Meta.get m u.t_map with
      | exception Not_found -> t
      | t' -> term_subst_aux u t'
    end
  | { Expr.term = Expr.App (f, tys, args) } as t ->
    let new_tys = List.map (type_subst u) tys in
    let new_args = List.map (term_subst_aux u) args in
    if List.for_all2 (==) tys new_tys && List.for_all2 (==) args new_args then t
    else Expr.Term.apply f new_tys new_args

let term_subst u t =
  if is_empty u then t else term_subst_aux u t

(* Fixpoint on meta substitutions *)
let fixpoint u = {
  ty_map = Expr.Subst.fold (fun m t acc ->
      Expr.Subst.Meta.bind acc m (type_subst u t)) u.ty_map Expr.Subst.empty;
  t_map = Expr.Subst.fold (fun m t acc ->
      Expr.Subst.Meta.bind acc m (term_subst u t)) u.t_map Expr.Subst.empty;
}

(* Robinson unification *)
(* ************************************************************************ *)

module Robinson = struct

  exception Impossible_ty of Expr.ty * Expr.ty
  exception Impossible_term of Expr.term * Expr.term

  let rec ty subst s t =
    let s = follow_ty subst s in
    let t = follow_ty subst t in
    match s, t with
    | { Expr.ty = Expr.TyVar v },
      { Expr.ty = Expr.TyVar v' } ->
      if Expr.Id.equal v v' then
        subst
      else
        raise (Impossible_ty (s, t))
    | ({ Expr.ty = Expr.TyMeta v } as m), u
    | u, ({ Expr.ty = Expr.TyMeta v } as m) ->
      if Expr.Ty.equal m u then
        subst
      else if occurs_ty subst [v] u then
        raise (Impossible_ty (m, u))
      else
        bind_ty subst v u
    | { Expr.ty = Expr.TyApp (f, f_args) },
      { Expr.ty = Expr.TyApp (g, g_args) } ->
      if Expr.Id.equal f g then
        List.fold_left2 ty subst f_args g_args
      else
        raise (Impossible_ty (s, t))
    | _ ->
      raise (Impossible_ty (s, t))

  let rec term subst s t =
    let s = follow_term subst s in
    let t = follow_term subst t in
    match s, t with
    | { Expr.term = Expr.Var v },
      { Expr.term = Expr.Var v' } ->
      if Expr.Id.equal v v' then
        subst
      else
        raise (Impossible_term (s, t))
    | ({ Expr.term = Expr.Meta v } as m), u
    | u, ({ Expr.term = Expr.Meta v } as m) ->
      if Expr.Term.equal m u then
        subst
      else if occurs_term subst [v] u then
        raise (Impossible_term (m, u))
      else
        let subst' = ty subst Expr.(m.t_type) Expr.(u.t_type) in
        bind_term subst' v u
    | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
      { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
      if Expr.Id.equal f g then
        List.fold_left2 term
          (List.fold_left2 ty subst f_ty_args g_ty_args)
          f_t_args g_t_args
      else
        raise (Impossible_term (s, t))
    | _ ->
      raise (Impossible_term (s, t))

  let unify_ty ~section f s t =
    try
      f (ty empty s t)
    with Impossible_ty _ -> ()

  let unify_term ~section f s t =
    try
      f (term empty s t)
    with Impossible_ty _ | Impossible_term _ -> ()

  let find ~section s t =
    Util.enter_prof section;
    let res =
      try Some (term empty s t)
      with Impossible_ty _ | Impossible_term _ -> None
    in
    Util.exit_prof section;
    res

end

(* Combine substitutions *)
(* ************************************************************************ *)

let combine t t' =
  try
    Some (
      Expr.Subst.fold (fun key value s -> Robinson.term s (Expr.Term.of_meta key) value) t'.t_map (
        Expr.Subst.fold (fun key value s -> Robinson.ty s (Expr.Ty.of_meta key) value) t'.ty_map t))
  with Robinson.Impossible_ty _ | Robinson.Impossible_term _ -> None

(* Export unifiers as formulas *)
(* ************************************************************************ *)

let to_formula t =
  Expr.Subst.fold (fun m t f ->
      Expr.(Formula.(f_and [f; eq (Term.of_meta m) t])))
    t.t_map Expr.Formula.f_true

(* Caching (modulo meta switching) *)
(* ************************************************************************ *)

module Cache = struct

  exception Impossible_ty of Expr.ty * Expr.ty
  exception Impossible_term of Expr.term * Expr.term

  (* Operations on involutions *)
  let inv_map_ty u m1 m2 =
    try
      let t1 = get_ty u m1 in
      let t2 = Expr.Ty.of_meta m2 in
      if not (Expr.Ty.equal t1 t2) then
        raise (Impossible_ty (t1, t2))
      else
        u
    with Not_found ->
      bind_ty (bind_ty u m1 (Expr.Ty.of_meta m2)) m2 (Expr.Ty.of_meta m1)

  let inv_map_term u m1 m2 =
    try
      let t1 = get_term u m1 in
      let t2 = Expr.Term.of_meta m2 in
      if not (Expr.Term.equal t1 t2) then
        raise (Impossible_term (t1, t2))
      else
        u
    with Not_found ->
      bind_term (bind_term u m1 (Expr.Term.of_meta m2)) m2 (Expr.Term.of_meta m1)

  let meta_def m = Expr.Meta.ty_def m.Expr.meta_index
  let meta_ty_def m = Expr.Meta.ttype_def m.Expr.meta_index

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
          let tmp = meta_match_term empty s1 s2 in
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
