
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

exception Not_unifiable_ty of Expr.ty * Expr.ty
exception Not_unifiable_term of Expr.term * Expr.term

(* Metavariable protection *)
(* ************************************************************************ *)

let rec protect_term = function
    | { Expr.term = Expr.Meta m } -> Expr.term_meta (Expr.protect m)
    | { Expr.term = Expr.App (f, ty_l, t_l) } ->
      Expr.term_app f ty_l (List.map protect_term t_l)
    | t -> t

(* Unifiers *)
(* ************************************************************************ *)

(* Definition *)
type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}

let empty = { ty_map = Expr.Subst.empty; t_map = Expr.Subst.empty; }

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


(* Instanciation helpers *)
let free_args = function
  | { Expr.formula = Expr.All (_, args, _) }
  | { Expr.formula = Expr.Ex (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, args, _) } } -> args
  | _ -> assert false

let belong_ty m s =
    let aux e m' _ =
      let f = Expr.get_meta_ty_def Expr.(m'.meta_index) in
      List.exists (Expr.Ty.equal e) (fst (free_args f))
    in
    Expr.Subst.exists (aux (Expr.type_meta m)) s.ty_map

let belong_term m s =
    let aux e m' _ =
      let f = Expr.get_meta_def Expr.(m'.meta_index) in
      List.exists (Expr.Term.equal e) (snd (free_args f))
    in
    Expr.Subst.exists (aux (Expr.term_meta m)) s.t_map

let split s =
  let rec aux bind belongs acc m t = function
      | [] -> bind empty m t :: acc
      | s :: r ->
        if belongs m s then
          (bind s m t) :: (List.rev_append acc r)
        else
          aux bind belongs (s :: acc) m t r
  in
  Expr.Subst.fold (aux bind_term belong_term []) s.t_map
    (Expr.Subst.fold (aux bind_ty belong_ty []) s.ty_map [])

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

let unify_ty s t = robinson_ty empty s t
let unify_term s t = robinson_term empty s t

(* Robinson unification with Caching for term unification *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)

let cache = H.create 1007

let cached_unify s t =
  let key = Builtin.tuple [s; t] in
  try
      H.find cache key
  with Not_found ->
      let res = unify_term s t in
      H.add cache key res;
      res


