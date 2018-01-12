
(* Mapping or variables & meta-variables *)

module E = Expr
module S = Expr.Subst

(* Mapping definition *)
(* ************************************************************************ *)

type t = {
  (* memoized hash *)
  mutable hash : int;
  (* types *)
  ty_var : (E.Id.Ttype.t, E.ty) S.t;
  ty_meta : (E.Meta.Ttype.t, E.ty) S.t;
  (* terms *)
  t_var : (E.Id.Ty.t, E.term) S.t;
  t_meta : (E.Meta.Ty.t, E.term) S.t;
  (* formulas *)
  f_var : (E.Id.Ty.t, E.formula) S.t;
  f_meta : (E.Meta.Ty.t, E.formula) S.t;
}

let ty_var t = t.ty_var
let ty_meta t = t.ty_meta
let term_var t = t.t_var
let term_meta t = t.t_meta
let formula_var t = t.f_var
let formula_meta t = t.f_meta

let empty = {
  hash = -1;
  ty_var = S.empty;
  ty_meta = S.empty;
  t_var = S.empty;
  t_meta = S.empty;
  f_var = S.empty;
  f_meta = S.empty;
}

let is_empty_ty t =
  S.is_empty t.ty_var &&
  S.is_empty t.ty_meta

let is_empty t =
  is_empty_ty t &&
  S.is_empty t.t_var &&
  S.is_empty t.t_meta &&
  S.is_empty t.f_var &&
  S.is_empty t.f_meta

let hash_aux m =
  Hashtbl.hash (
    S.hash E.Ty.hash m.ty_var,
    S.hash E.Ty.hash m.ty_meta,
    S.hash E.Term.hash m.t_var,
    S.hash E.Term.hash m.t_meta,
    S.hash E.Formula.hash m.f_var,
    S.hash E.Formula.hash m.f_meta
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
  <?> (S.compare E.Formula.compare, m.f_var, m'.f_var)
  <?> (S.compare E.Formula.compare, m.f_meta, m'.f_meta)

let equal m m' = compare m m' = 0

let pp_sep s =
  CCFormat.return (if S.is_empty s then "" else ";@ ")

let print fmt m =
  Format.fprintf fmt "@[<hov 1>{%a%a%a%a%a%a%a%a%a%a%a}@]"
    (S.print E.Print.id E.Print.ty) m.ty_var (pp_sep m.ty_var) ()
    (S.print E.Print.meta E.Print.ty) m.ty_meta (pp_sep m.ty_meta) ()
    (S.print E.Print.id E.Print.term) m.t_var (pp_sep m.t_var) ()
    (S.print E.Print.meta E.Print.term) m.t_meta (pp_sep m.t_meta) ()
    (S.print E.Print.id E.Print.formula) m.f_var (pp_sep m.t_var) ()
    (S.print E.Print.meta E.Print.formula) m.f_meta


(* Whole mapping functions *)
(* ************************************************************************ *)

(* Helper functions *)
let _id _ _ acc = acc
let _false _ _ = false
let _assert_false2 _ _ = assert false
let _assert_false3 _ _ _ = assert false


(* Interesting functions *)

let map f_ty f_term f_formula t = {
  hash = -1;
  ty_var = S.map f_ty t.ty_var;
  ty_meta = S.map f_ty t.ty_meta;
  t_var = S.map f_term t.t_var;
  t_meta = S.map f_term t.t_meta;
  f_var = S.map f_formula t.f_var;
  f_meta = S.map f_formula t.f_meta;
}


let fold
  ?(ty_var=_id)
  ?(ty_meta=_id)
  ?(term_var=_id)
  ?(term_meta=_id)
  ?(formula_var=_id)
  ?(formula_meta=_id) t acc =
  S.fold ty_var t.ty_var @@
  S.fold ty_meta t.ty_meta @@
  S.fold term_var t.t_var @@
  S.fold term_meta t.t_meta @@
  S.fold formula_var t.f_var @@
  S.fold formula_meta t.f_meta acc

let for_all
    ?(ty_var=_false)
    ?(ty_meta=_false)
    ?(term_var=_false)
    ?(term_meta=_false)
    ?(formula_var=_false)
    ?(formula_meta=_false) t =
  S.for_all ty_var t.ty_var &&
  S.for_all ty_meta t.ty_meta &&
  S.for_all term_var t.t_var &&
  S.for_all term_meta t.t_meta &&
  S.for_all formula_var t.f_var &&
  S.for_all formula_meta t.f_meta

let exists
    ?(ty_var=_false)
    ?(ty_meta=_false)
    ?(term_var=_false)
    ?(term_meta=_false)
    ?(formula_var=_false)
    ?(formula_meta=_false) t =
  S.exists ty_var t.ty_var ||
  S.exists ty_meta t.ty_meta ||
  S.exists term_var t.t_var ||
  S.exists term_meta t.t_meta ||
  S.exists formula_var t.f_var ||
  S.exists formula_meta t.f_meta

let filter
    ?(ty_var=_assert_false2)
    ?(ty_meta=_assert_false2)
    ?(term_var=_assert_false2)
    ?(term_meta=_assert_false2)
    ?(formula_var=_assert_false2)
    ?(formula_meta=_assert_false2) t =
  { hash = -1;
    ty_var = S.filter ty_var t.ty_var;
    ty_meta = S.filter ty_meta t.ty_meta;
    t_var = S.filter term_var t.t_var;
    t_meta = S.filter term_meta t.t_meta;
    f_var = S.filter formula_var t.f_var;
    f_meta = S.filter formula_meta t.f_meta;
  }

let merge
    ?(ty_var=_assert_false3)
    ?(ty_meta=_assert_false3)
    ?(term_var=_assert_false3)
    ?(term_meta=_assert_false3)
    ?(formula_var=_assert_false3)
    ?(formula_meta=_assert_false3) t t' =
  { hash = -1;
    ty_var = S.merge ty_var t.ty_var t'.ty_var;
    ty_meta = S.merge ty_meta t.ty_meta t'.ty_meta;
    t_var = S.merge term_var t.t_var t'.t_var;
    t_meta = S.merge term_meta t.t_meta t'.t_meta;
    f_var = S.merge formula_var t.f_var t'.f_var;
    f_meta = S.merge formula_meta t.f_meta t'.f_meta;
  }

(* Mapping domain *)
(* ************************************************************************ *)

let domain m =
  fold m (([], []), ([], []))
    ~ty_var:(fun v _ (vars, metas) -> Expr.Id.merge_fv vars ([v], []), metas)
    ~ty_meta:(fun m _ (vars, metas) -> vars, Expr.Meta.merge_fm metas ([m], []))
    ~term_var:(fun v _ (vars, metas) -> Expr.Id.merge_fv vars ([], [v]), metas)
    ~term_meta:(fun m _ (vars, metas) -> vars, Expr.Meta.merge_fm metas ([], [m]))
    ~formula_var:(fun v _ (vars, metas) -> Expr.Id.merge_fv vars ([], [v]), metas)
    ~formula_meta:(fun m _ (vars, metas) -> vars, Expr.Meta.merge_fm metas ([], [m]))

(* Mapping co-domain *)
(* ************************************************************************ *)

let codomain m =
  let aux_ty _ ty (v,m) = Expr.Id.merge_fv v (Expr.Ty.fv ty),
                          Expr.Meta.merge_fm m (Expr.Ty.fm ty) in
  let aux_term _ term (v,m) = Expr.Id.merge_fv v (Expr.Term.fv term),
                              Expr.Meta.merge_fm m (Expr.Term.fm term) in
  let aux_formula _ f (v, m) = Expr.Id.merge_fv v (Expr.Formula.fv f),
                               Expr.Meta.merge_fm m (Expr.Formula.fm f) in
  fold
    ~ty_var:aux_ty ~ty_meta:aux_ty
    ~term_var:aux_term ~term_meta:aux_term
    ~formula_var:aux_formula ~formula_meta:aux_formula
    m (([], []), ([], []))

(* Variable bindings *)
(* ************************************************************************ *)

module Var = struct

  let mem_ty t v = S.Id.mem v t.ty_var
  let mem_term t v = S.Id.mem v t.t_var
  let mem_formula t v = S.Id.mem v t.f_var

  let get_ty t v = S.Id.get v t.ty_var
  let get_term t v = S.Id.get v t.t_var
  let get_formula t v = S.Id.get v t.f_var

  let get_ty_opt t v =
    try Some (get_ty t v)
    with Not_found -> None

  let get_term_opt t v =
    try Some (get_term t v)
    with Not_found -> None

  let get_formula_opt t v =
    assert Expr.(Ty.equal v.id_type Ty.prop);
    try Some (get_formula t v)
    with Not_found -> None

  let bind_ty t v ty =
    { t with hash = -1; ty_var = S.Id.bind t.ty_var v ty }

  let bind_term t v term =
    { t with hash = -1; t_var = S.Id.bind t.t_var v term }

  let bind_formula t v formula =
    assert Expr.(Ty.equal v.id_type Ty.prop);
    { t with hash = -1; f_var = S.Id.bind t.f_var v formula }

end

(* Meta-variable bindings *)
(* ************************************************************************ *)

module Meta = struct

  let mem_ty t m = S.Meta.mem m t.ty_meta
  let mem_term t m = S.Meta.mem m t.t_meta
  let mem_formula t m = S.Meta.mem m t.f_meta

  let get_ty t m = S.Meta.get m t.ty_meta
  let get_term t m = S.Meta.get m t.t_meta
  let get_formula t m = S.Meta.get m t.f_meta

  let get_ty_opt t m =
    try Some (get_ty t m)
    with Not_found -> None

  let get_term_opt t m =
    try Some (get_term t m)
    with Not_found -> None

  let get_formula_opt t m =
    assert Expr.(Ty.equal m.meta_id.id_type Ty.prop);
    try Some (get_formula t m)
    with Not_found -> None

  let bind_ty t m ty =
    { t with hash = -1; ty_meta = S.Meta.bind t.ty_meta m ty }

  let bind_term t m term =
    { t with hash = -1; t_meta = S.Meta.bind t.t_meta m term }

  let bind_formula t m formula =
    assert Expr.(Ty.equal m.meta_id.id_type Ty.prop);
    { t with hash = -1; f_meta = S.Meta.bind t.f_meta m formula }

end

(* Mappings operations *)
(* ************************************************************************ *)

let remove_refl m =
  filter
    ~ty_var:(fun v ty -> not @@ Expr.Ty.(equal ty @@ of_id v))
    ~ty_meta:(fun m ty -> not @@ Expr.Ty.(equal ty @@ of_meta m))
    ~term_var:(fun v term -> not @@ Expr.Term.(equal term @@ of_id v))
    ~term_meta:(fun m term -> not @@ Expr.Term.(equal term @@ of_meta m))
    ~formula_var:(fun v formula -> not @@ Expr.Formula.(
        equal formula @@ pred Expr.Term.(of_id v)))
    ~formula_meta:(fun v formula -> not @@ Expr.Formula.(
        equal formula @@ pred Expr.Term.(of_meta v)))
    m

(* Mappings as substitution *)
(* ************************************************************************ *)

let apply_ty ?fix t ty =
  Expr.Ty.subst ?fix t.ty_var t.ty_meta ty

let apply_term ?fix t term =
  Expr.Term.subst ?fix t.ty_var t.ty_meta t.t_var t.t_meta term

let apply_formula ?fix t formula =
  Expr.Formula.subst ?fix formula
    ~ty_var_map:t.ty_var ~ty_meta_map:t.ty_meta
    ~t_var_map:t.t_var ~t_meta_map:t.t_meta
    ~f_var_map:t.f_var ~f_meta_map:t.f_meta

let apply ?fix t m =
  map (apply_ty ?fix t) (apply_term ?fix t) (apply_formula ?fix t) m

(* Fixpoint on meta substitutions *)
let fixpoint t =
  Util.debug "Fixpoint: %a" print t;
  apply ~fix:true t t

(* Mapping completion *)
(* ************************************************************************ *)

(* When unifying or building mapping, it might happen that there are
   type variable bindings that changes the type of a term variable that
   doesn't appear in the mapping, in which case these variables should be added
   to the substitution. For instance, it happens that we get a mapping:
   { alpha -> ty; x (of type alpha) -> y }, with y a variable of type alpha,
   in which case the mapping should be extended with: y (: alpha) -> y (: ty).
   This funciton completes a mapping in this way, with regards to a list
   of variables (kinda like in the way quantified variables are renamed. *)
let extend m l =
  let aux acc v =
    let old_ty = v.Expr.id_type in
    let new_ty = apply_ty acc old_ty in
    if Expr.Ty.equal old_ty new_ty || Var.mem_term acc v
    then acc
    else Var.bind_term acc v
        (Expr.Term.of_id @@ Expr.Id.ty v.Expr.id_name new_ty)
  in
  List.fold_left aux m l

let expand m t =
  let _, l = Expr.Term.fv t in
  extend m l

let complete m =
  let ((_, l), _) = codomain m in
  extend m l



