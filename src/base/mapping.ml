
(* Mapping or variables & meta-variables *)

module E = Expr
module S = Expr.Subst

(* Mapping definition *)
(* ************************************************************************ *)

type t = {
  mutable hash : int;
  (* types *)
  ty_var : (E.Id.Ttype.t, E.ty) S.t;
  ty_meta : (E.Meta.Ttype.t, E.ty) S.t;
  (* terms *)
  t_var : (E.Id.Ty.t, E.term) S.t;
  t_meta : (E.Meta.Ty.t, E.term) S.t;
}

let ty_var t = t.ty_var
let ty_meta t = t.ty_meta
let term_var t = t.t_var
let term_meta t = t.t_meta

let empty = {
  hash = -1;
  ty_var = S.empty;
  ty_meta = S.empty;
  t_var = S.empty;
  t_meta = S.empty;
}

let is_empty_ty t =
  S.is_empty t.ty_var &&
  S.is_empty t.ty_meta

let is_empty t =
  is_empty_ty t &&
  S.is_empty t.t_var &&
  S.is_empty t.t_meta

let hash_aux m =
  Hashtbl.hash (
    S.hash E.Ty.hash m.ty_var,
    S.hash E.Ty.hash m.ty_meta,
    S.hash E.Term.hash m.t_var,
    S.hash E.Term.hash m.t_meta
  )

let hash m =
  if m.hash < 0 then
    let res = hash_aux m in
    m.hash <- res;
    res
  else
    m.hash

let compare m m' =
  let open CCOrd.Infix in
  S.compare E.Ty.compare m.ty_var m'.ty_var
  <?> (S.compare E.Ty.compare, m.ty_meta, m'.ty_meta)
  <?> (S.compare E.Term.compare, m.t_var, m'.t_var)
  <?> (S.compare E.Term.compare, m.t_meta, m'.t_meta)

let equal m m' = compare m m' = 0

let pp_sep s =
  CCFormat.return (if S.is_empty s then "" else ";@ ")

let print fmt m =
  Format.fprintf fmt "@[<hov 1>{%a%a%a%a%a%a%a}@]"
    (S.print E.Print.id E.Print.ty) m.ty_var (pp_sep m.ty_var) ()
    (S.print E.Print.meta E.Print.ty) m.ty_meta (pp_sep m.ty_meta) ()
    (S.print E.Print.id E.Print.term) m.t_var (pp_sep m.t_var) ()
    (S.print E.Print.meta E.Print.term) m.t_meta

(* Whole mapping functions *)
(* ************************************************************************ *)

let map f_ty f_term t = {
  hash = -1;
  ty_var = S.map f_ty t.ty_var;
  ty_meta = S.map f_ty t.ty_meta;
  t_var = S.map f_term t.t_var;
  t_meta = S.map f_term t.t_meta;
}

let _id _ _ acc = acc
let _false _ _ = false

let fold
  ?(ty_var=_id)
  ?(ty_meta=_id)
  ?(term_var=_id)
  ?(term_meta=_id) t acc =
  S.fold ty_var t.ty_var @@
  S.fold ty_meta t.ty_meta @@
  S.fold term_var t.t_var @@
  S.fold term_meta t.t_meta acc

let for_all
    ?(ty_var=_false)
    ?(ty_meta=_false)
    ?(term_var=_false)
    ?(term_meta=_false) t =
  S.for_all ty_var t.ty_var &&
  S.for_all ty_meta t.ty_meta &&
  S.for_all term_var t.t_var &&
  S.for_all term_meta t.t_meta

let exists
    ?(ty_var=_false)
    ?(ty_meta=_false)
    ?(term_var=_false)
    ?(term_meta=_false) t =
  S.exists ty_var t.ty_var &&
  S.exists ty_meta t.ty_meta &&
  S.exists term_var t.t_var &&
  S.exists term_meta t.t_meta

(* Variable bindings *)
(* ************************************************************************ *)

module Var = struct

  let mem_ty t v = S.Id.mem v t.ty_var
  let mem_term t v = S.Id.mem v t.t_var

  let get_ty t v = S.Id.get v t.ty_var
  let get_term t v = S.Id.get v t.t_var

  let get_ty_opt t v =
    try Some (get_ty t v)
    with Not_found -> None

  let get_term_opt t v =
    try Some (get_term t v)
    with Not_found -> None

  let bind_ty t v ty =
    { t with ty_var = S.Id.bind t.ty_var v ty }

  let bind_term t v term =
    { t with t_var = S.Id.bind t.t_var v term }

end

(* Meta-variable bindings *)
(* ************************************************************************ *)

module Meta = struct

  let mem_ty t m = S.Meta.mem m t.ty_meta
  let mem_term t m = S.Meta.mem m t.t_meta

  let get_ty t m = S.Meta.get m t.ty_meta
  let get_term t m = S.Meta.get m t.t_meta

  let get_ty_opt t m =
    try Some (get_ty t m)
    with Not_found -> None

  let get_term_opt t m =
    try Some (get_term t m)
    with Not_found -> None

  let bind_ty t m ty =
    { t with ty_meta = S.Meta.bind t.ty_meta m ty }

  let bind_term t m term =
    { t with t_meta = S.Meta.bind t.t_meta m term }

end

(* Mappings as substitution *)
(* ************************************************************************ *)

let rec apply_ty_aux ~fix t = function
  | { Expr.ty = Expr.TyVar v } as ty ->
    begin match Var.get_ty t v with
      | exception Not_found -> ty
      | ty' ->
        if fix then apply_ty_aux ~fix t ty' else ty'
    end
  | { Expr.ty = Expr.TyMeta m } as ty ->
    begin match Meta.get_ty t m with
    | exception Not_found -> ty
    | ty' ->
      if fix then apply_ty_aux ~fix t ty' else ty'
    end
  | { Expr.ty = Expr.TyApp (f, args) } as ty ->
    let new_args = List.map (apply_ty_aux ~fix t) args in
    if List.for_all2 (==) args new_args then ty
    else Expr.Ty.apply f new_args

let apply_ty ~fix t ty =
  if is_empty_ty t then ty else apply_ty_aux ~fix t ty

let rec apply_term_aux ~fix t = function
  | { Expr.term = Expr.Var v } as term ->
    begin match Var.get_term t v with
      | exception Not_found -> term
      | term' ->
        if fix then apply_term_aux ~fix t term' else term'
    end
  | { Expr.term = Expr.Meta m } as term ->
    begin match Meta.get_term t m with
      | exception Not_found -> term
      | term' ->
        if fix then apply_term_aux ~fix t term' else term'
    end
  | { Expr.term = Expr.App (f, tys, args) } as term ->
    let new_tys = List.map (apply_ty ~fix t) tys in
    let new_args = List.map (apply_term_aux ~fix t) args in
    if List.for_all2 (==) tys new_tys && List.for_all2 (==) args new_args then term
    else Expr.Term.apply f new_tys new_args

let apply_term ~fix t term =
  if is_empty t then term else apply_term_aux ~fix t term

(* Fixpoint on meta substitutions *)
let fixpoint t = map (apply_ty ~fix:true t) (apply_term ~fix:true t) t



