
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

exception Not_unifiable_ty of Expr.ty * Expr.ty
exception Not_unifiable_term of Expr.term * Expr.term

let log_section = Util.Section.make "unif"
let log i fmt = Util.debug ~section:log_section i fmt

(* Unifiers *)
(* ************************************************************************ *)

(* Definition *)
type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}

let empty = { ty_map = Expr.Subst.empty; t_map = Expr.Subst.empty; }

let mem_ty subst m = Expr.Subst.Meta.mem m subst.ty_map
let mem_term subst m = Expr.Subst.Meta.mem m subst.t_map

let get_ty subst m = Expr.Subst.Meta.get m subst.ty_map
let get_term subst m = Expr.Subst.Meta.get m subst.t_map

let bind_ty subst m t = { subst with ty_map = Expr.Subst.Meta.bind m t subst.ty_map }
let bind_term subst m t = { subst with t_map = Expr.Subst.Meta.bind m t subst.t_map }

let hash s =
  Hashtbl.hash (Expr.Subst.hash Expr.Ty.hash s.ty_map, Expr.Subst.hash Expr.Term.hash s.t_map)

let compare s u =
  match Expr.Subst.compare Expr.Ty.compare s.ty_map u.ty_map with
  | 0 -> Expr.Subst.compare Expr.Term.compare s.t_map u.t_map
  | x -> x

let equal s u =
    Expr.Subst.equal Expr.Ty.equal s.ty_map u.ty_map &&
    Expr.Subst.equal Expr.Term.equal s.t_map u.t_map

let merge s s' = {
    ty_map = Expr.Subst.fold Expr.Subst.Meta.bind s.ty_map s'.ty_map;
    t_map = Expr.Subst.fold Expr.Subst.Meta.bind s.t_map s'.t_map;
}

(* Metavariable protection *)
(* ************************************************************************ *)

let rec protect_ty = function
    | { Expr.ty = Expr.TyVar _ } as ty -> ty
    | { Expr.ty = Expr.TyMeta m } -> Expr.type_meta (Expr.protect m)
    | { Expr.ty = Expr.TyApp (f, ty_l) } ->
      Expr.type_app f (List.map protect_ty ty_l)

let rec protect_term = function
    | { Expr.term = Expr.Var _ } as t -> t
    | { Expr.term = Expr.Meta m } -> Expr.term_meta (Expr.protect m)
    | { Expr.term = Expr.App (f, ty_l, t_l) } ->
      Expr.term_app f (List.map protect_ty ty_l) (List.map protect_term t_l)

let protect_inst s = {
    ty_map = Expr.Subst.fold (fun m ty acc ->
        Expr.Subst.Meta.bind m (protect_ty ty) acc) s.ty_map Expr.Subst.empty;
    t_map = Expr.Subst.fold (fun m t acc ->
        Expr.Subst.Meta.bind m (protect_term t) acc) s.t_map Expr.Subst.empty;
}

(* Manipulation over meta substitutions *)
(* ************************************************************************ *)

(* Substitutes meta instead of variables *)
let rec type_subst_aux map = function
  | { Expr.ty = Expr.TyVar _ } -> assert false
  | { Expr.ty = Expr.TyMeta m } as t ->
    begin try Expr.Subst.Meta.get m map with Not_found -> t end
  | { Expr.ty = Expr.TyApp (f, args) } ->
    Expr.type_app f (List.map (type_subst_aux map) args)

let type_subst map t = if Expr.Subst.is_empty map then t else type_subst_aux map t

let rec term_subst_aux ty_map t_map = function
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta m } as t ->
    begin try Expr.Subst.Meta.get m t_map with Not_found -> t end
  | { Expr.term = Expr.App (f, tys, args) } ->
    Expr.term_app f (List.map (type_subst ty_map) tys) (List.map (term_subst_aux ty_map t_map) args)

let term_subst ty_map t_map t =
  if Expr.Subst.is_empty ty_map && Expr.Subst.is_empty t_map then
      t
  else
      term_subst_aux ty_map t_map t

(* Fixpoint on meta substitutions *)
let fixpoint u =
    let rec ty_apply ty =
        let ty' = type_subst u.ty_map ty in
        if Expr.Ty.equal ty ty' then ty
        else ty_apply ty'
    in
    let rec t_apply t =
        let t' = term_subst u.ty_map u.t_map t in
        if Expr.Term.equal t t' then t
        else t_apply t'
    in
    {
        ty_map = Expr.Subst.fold (fun m t acc -> Expr.Subst.Meta.bind m (ty_apply t) acc) u.ty_map Expr.Subst.empty;
        t_map = Expr.Subst.fold (fun m t acc -> Expr.Subst.Meta.bind m (t_apply t) acc) u.t_map Expr.Subst.empty;
    }

(* Meta-matching *)
(* ************************************************************************ *)

(* Operations on involutions *)
let inv_map_ty u m1 m2 =
    try
        let t1 = get_ty u m1 in
        let t2 = Expr.type_meta m2 in
        if not (Expr.Ty.equal t1 t2) then
            raise (Not_unifiable_ty (t1, t2))
        else
            u
    with Not_found ->
        bind_ty (bind_ty u m1 (Expr.type_meta m2)) m2 (Expr.type_meta m1)

let inv_map_term u m1 m2 =
    try
        let t1 = get_term u m1 in
        let t2 = Expr.term_meta m2 in
        if not (Expr.Term.equal t1 t2) then
            raise (Not_unifiable_term (t1, t2))
        else
            u
    with Not_found ->
        bind_term (bind_term u m1 (Expr.term_meta m2)) m2 (Expr.term_meta m1)

(* Finding meta-stable involutions *)
let rec meta_match_ty subst s t =
      begin match s, t with
        | _, { Expr.ty = Expr.TyVar _ } | { Expr.ty = Expr.TyVar _}, _ -> assert false
        | { Expr.ty = Expr.TyMeta ({ Expr.meta_var = v1 } as m1)},
          { Expr.ty = Expr.TyMeta ({ Expr.meta_var = v2 } as m2)} ->
          if Expr.Var.equal v1 v2 then
            inv_map_ty subst m1 m2
          else
              raise (Not_unifiable_ty (s, t))
        | { Expr.ty = Expr.TyApp (f, f_args) },
          { Expr.ty = Expr.TyApp (g, g_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 meta_match_ty subst f_args g_args
          else
            raise (Not_unifiable_ty (s, t))
        | _ -> raise (Not_unifiable_ty (s, t))
      end

let rec meta_match_term subst s t =
    log 90 "trying %a <-> %a" Expr.debug_term s Expr.debug_term t;
      begin match s, t with
        | _, { Expr.term = Expr.Var _ } | { Expr.term = Expr.Var _}, _ -> assert false
        | { Expr.term = Expr.Meta ({ Expr.meta_var = v1 } as m1) },
          { Expr.term = Expr.Meta ({ Expr.meta_var = v2 } as m2)} ->
          if Expr.Var.equal v1 v2 then
            inv_map_term subst m1 m2
          else
              raise (Not_unifiable_term (s, t))
        | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
          { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 meta_match_term
              (List.fold_left2 meta_match_ty subst f_ty_args g_ty_args)
              f_t_args g_t_args
          else
            raise (Not_unifiable_term (s, t))
        | _ -> raise (Not_unifiable_term (s, t))
      end

(*
let match_ty_meta s t = meta_match_ty empty s t
let match_term_meta s t = meta_match_term empty s t

let equal_up_to_metas u u' =
    try
        let _ = Expr.Subst.fold (fun m t acc -> meta_match_term acc (get_term u' m) t) u.t_map
               (Expr.Subst.fold (fun m ty acc -> meta_match_ty acc (get_ty u' m) ty) u.ty_map empty)
        in
        true
    with Not_found | Not_unifiable_ty _ | Not_unifiable_term _ ->
        false
*)

(* Robinson unification *)
(* ************************************************************************ *)

let follow_ty subst = function
  | { Expr.ty = Expr.TyMeta m } -> get_ty subst m
  | _ -> raise Not_found

let follow_term subst = function
  | { Expr.term = Expr.Meta m } -> get_term subst m
  | _ -> raise Not_found

let rec occurs_check_ty subst v = function
    | { Expr.ty = Expr.TyMeta m } as v' ->
      begin try occurs_check_ty subst v (get_ty subst m)
      with Not_found -> Expr.Ty.equal v v' end
    | { Expr.ty = Expr.TyApp (f, l) } -> List.exists (occurs_check_ty subst v) l
    | _ -> false

let rec occurs_check_term subst v = function
    | { Expr.term = Expr.Meta m } as v' ->
      begin try occurs_check_term subst v (get_term subst m)
      with Not_found -> Expr.Term.equal v v' end
    | { Expr.term= Expr.App (f, _, l) } -> List.exists (occurs_check_term subst v) l
    | _ -> false

let rec robinson_ty subst s t =
    try robinson_ty subst (follow_ty subst s) t with Not_found ->
    try robinson_ty subst s (follow_ty subst t) with Not_found ->
      begin match s, t with
        | _ when Expr.Ty.equal s t -> subst
        | _, { Expr.ty = Expr.TyVar _ } | { Expr.ty = Expr.TyVar _}, _ -> assert false
        | ({ Expr.ty = Expr.TyMeta ({Expr.can_unify= true} as v) } as m), u
        | u, ({ Expr.ty = Expr.TyMeta ({Expr.can_unify = true} as v) } as m) ->
          if occurs_check_ty subst m u then
            raise (Not_unifiable_ty (m, u))
          else
            bind_ty subst v u
        | { Expr.ty = Expr.TyApp (f, f_args) },
          { Expr.ty = Expr.TyApp (g, g_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 robinson_ty subst f_args g_args
          else
            raise (Not_unifiable_ty (s, t))
        | _ -> raise (Not_unifiable_ty (s, t))
      end

let rec robinson_term subst s t =
    try robinson_term subst (follow_term subst s) t with Not_found ->
    try robinson_term subst s (follow_term subst t) with Not_found ->
      begin match s, t with
        | _ when Expr.Term.equal s t -> subst
        | _, { Expr.term = Expr.Var _ } | { Expr.term = Expr.Var _}, _ -> assert false
        | ({ Expr.term = Expr.Meta ({Expr.can_unify= true} as v) } as m), u
        | u, ({ Expr.term = Expr.Meta ({Expr.can_unify = true} as v) } as m) ->
          if occurs_check_term subst m u then
            raise (Not_unifiable_term (m, u))
          else
            bind_term subst v u
        | { Expr.term = Expr.App (f, f_ty_args, f_t_args) },
          { Expr.term = Expr.App (g, g_ty_args, g_t_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 robinson_term
              (List.fold_left2 robinson_ty subst f_ty_args g_ty_args)
              f_t_args g_t_args
          else
            raise (Not_unifiable_term (s, t))
        | _ -> raise (Not_unifiable_term (s, t))
      end

let unify_ty s t = fixpoint (robinson_ty empty s t)
let unify_term s t = fixpoint (robinson_term empty s t)

(* Robinson unification with Caching (modulo meta switching) for term unification *)
(* ************************************************************************ *)

module H = Hashtbl.Make(struct
    type t = Expr.term * Expr.term
    let hash (s, t) = Hashtbl.hash (Expr.Term.hash s, Expr.Term.hash t)
    let equal (s1, t1) (s2, t2) =
        try
            let tmp = meta_match_term empty s1 s2 in
            let _ = meta_match_term tmp t1 t2 in
            true
        with Not_unifiable_ty _ | Not_unifiable_term _ ->
            false
end)

let cache = H.create 4096

let cached_unify s t =
  let key = (s, t) in
  try
      H.find cache key
  with Not_found ->
      let res = unify_term s t in
      H.add cache key res;
      res

