
(* Matching module *)

(* Substitutions *)
(* ************************************************************************ *)

type t = {
  ty_map : (Expr.ttype Expr.id, Expr.ty) Expr.Subst.t;
  t_map  : (Expr.ty Expr.id, Expr.term) Expr.Subst.t;
}

let empty = {
  ty_map = Expr.Subst.empty;
  t_map = Expr.Subst.empty;
}

let is_empty u =
  Expr.Subst.is_empty u.ty_map &&
  Expr.Subst.is_empty u.t_map

let mem_ty subst m = Expr.Subst.Id.mem m subst.ty_map
let mem_term subst m = Expr.Subst.Id.mem m subst.t_map

let get_ty subst m = Expr.Subst.Id.get m subst.ty_map
let get_term subst m = Expr.Subst.Id.get m subst.t_map

let get_ty_opt subst m =
  try Some (Expr.Subst.Id.get m subst.ty_map)
  with Not_found -> None

let get_term_opt subst m =
  try Some (Expr.Subst.Id.get m subst.t_map)
  with Not_found -> None

let bind_ty subst m t =
  { subst with ty_map = Expr.Subst.Id.bind subst.ty_map m t }
let bind_term subst m t =
  { subst with t_map = Expr.Subst.Id.bind subst.t_map m t }

let hash s =
  Hashtbl.hash (
    Expr.Subst.hash Expr.Ty.hash s.ty_map,
    Expr.Subst.hash Expr.Term.hash s.t_map
  )

let compare s u =
  match Expr.Subst.compare Expr.Ty.compare s.ty_map u.ty_map with
  | 0 -> Expr.Subst.compare Expr.Term.compare s.t_map u.t_map
  | x -> x

let equal s u =
  Expr.Subst.equal Expr.Ty.equal s.ty_map u.ty_map &&
  Expr.Subst.equal Expr.Term.equal s.t_map u.t_map

let debug b s =
  Printf.bprintf b "{%a; %a}"
    (Expr.Subst.debug Expr.Debug.id Expr.Debug.ty) s.ty_map
    (Expr.Subst.debug Expr.Debug.id Expr.Debug.term) s.t_map

let print fmt s =
  Format.fprintf fmt "{%a; %a}"
    (Expr.Subst.print Expr.Print.id Expr.Print.ty) s.ty_map
    (Expr.Subst.print Expr.Print.id Expr.Print.term) s.t_map

(* Manipulation over variable substitutions *)
(* ************************************************************************ *)

(* Fixpoint voer variable substitution *)
let rec type_subst_aux ~fix u = function
  | { Expr.ty = Expr.TyVar v } as t ->
    begin match get_ty u v with
    | exception Not_found -> t
    | t' -> if fix then type_subst_aux ~fix u t' else t'
    end
  | { Expr.ty = Expr.TyMeta _ } as t -> t
  | { Expr.ty = Expr.TyApp (f, args) } as ty ->
    let new_args = List.map (type_subst_aux ~fix u) args in
    if List.for_all2 (==) args new_args then ty
    else Expr.Ty.apply f new_args

let type_apply u t =
  if Expr.Subst.is_empty u.ty_map then t
  else type_subst_aux ~fix:false u t

let type_subst u t =
  if Expr.Subst.is_empty u.ty_map then t
  else type_subst_aux ~fix:true u t

let rec term_subst_aux ~fix u = function
  | { Expr.term = Expr.Var v } as t ->
    begin match get_term u v with
      | exception Not_found -> t
      | t' -> if fix then term_subst_aux ~fix u t' else t'
    end
  | { Expr.term = Expr.Meta _ } as t -> t
  | { Expr.term = Expr.App (f, tys, args) } as t ->
    let new_tys = List.map (type_subst u) tys in
    let new_args = List.map (term_subst_aux ~fix u) args in
    if List.for_all2 (==) tys new_tys && List.for_all2 (==) args new_args then t
    else Expr.Term.apply f new_tys new_args

let term_apply u t =
  if is_empty u then t
  else term_subst_aux ~fix:false u t

let term_subst u t =
  if is_empty u then t
  else term_subst_aux ~fix:true u t

(* Fixpoint on meta substitutions *)
let fixpoint u = {
  ty_map = Expr.Subst.fold (fun m t acc ->
      Expr.Subst.Id.bind acc m (type_subst u t)) u.ty_map Expr.Subst.empty;
  t_map = Expr.Subst.fold (fun m t acc ->
      Expr.Subst.Id.bind acc m (term_subst u t)) u.t_map Expr.Subst.empty;
}

(* Matching algorithm *)
(* ************************************************************************ *)

exception Impossible_ty of Expr.ty * Expr.ty
exception Impossible_term of Expr.term * Expr.term

let rec ty subst pat t =
  match pat, t with
  | { Expr.ty = Expr.TyVar v }, _ ->
    begin match get_ty_opt subst v with
      | Some t' ->
        if Expr.Ty.equal t t' then subst
        else raise (Impossible_ty (pat, t))
      | None ->
        bind_ty subst v t
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
    begin match get_term_opt subst v with
      | Some t' ->
        if Expr.Term.equal t t' then subst
        else raise (Impossible_term (pat, t))
      | None ->
        let subst' = ty subst Expr.(pat.t_type) Expr.(t.t_type) in
        let subst'' = bind_term subst' v t in
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

let find ~section pat t =
  Util.enter_prof section;
  let res =
    try Some (term empty pat t)
    with Impossible_ty _ | Impossible_term _ -> None
  in
  Util.exit_prof section;
  res

