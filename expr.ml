

(* Type definitions *)
(* ************************************************************************ *)

(* Variables, parametrized by the kind of the type of the variable *)
type 'ty var = {
    var_name : string;
    var_id : int; (* unique *)
    var_type : 'ty;
}

type 'ty meta = {
    meta_var : 'ty var;
    meta_index : int;
    (* vector index of the formula corresponding to the meta *)
}

type 'ty id = 'ty var

(* Type for first order types *)
type ttype = Type

type ty_descr =
    | TyVar of ttype var
    | TyMeta of ttype meta
    | TyApp of ttype function_descr id * ty list

and ty = {
    ty : ty_descr;
    mutable ty_hash : int;
}

and 'ty function_descr = {
    fun_vars : 'ty var list; (* prenex forall *)
    fun_args : 'ty list;
    fun_ret : 'ty;
}

(* Terms & formulas *)
type term_descr =
    | Var of ty var
    | Meta of ty meta
    | App of ty function_descr id * ty list * term list

and term = {
    term    : term_descr;
    t_type  : ty;
    mutable t_hash : int; (* lazy hash *)
    t_constr : (ty var * formula list) option;
    (* Constrained expression equal to var that verifies the formulas given *)
}

and formula_descr =
    (* Atoms *)
    | Equal of term * term (* + ty ? *)
    | Pred of term

    (* Prop constructors *)
    | Not of formula
    | And of formula list
    | Or of formula list
    | Imply of formula * formula
    | Equiv of formula * formula

    (* Quantifiers *)
    | All of ty var list * formula
    | AllTy of ttype var list * formula
    | Ex of ty var list * formula

and formula = {
    formula : formula_descr;
    mutable f_hash  : int; (* lazy hash *)
}

(* Hashs *)
(* ************************************************************************ *)

let rec hash_ty t =
    let h = match t.ty with
        | TyVar v -> v.var_id
        | TyMeta v -> v.meta_var.var_id
        | TyApp (f, args) -> (* TODO: Better combinator ? *)
                Hashtbl.hash (f.var_id ::
                    (List.rev_map get_ty_hash args))
    in
    t.ty_hash <- h

and get_ty_hash t =
    if t.ty_hash = -1 then hash_ty t;
    assert (t.ty_hash >= 0);
    t.ty_hash

let rec hash_term t =
    let h = match t.term with
        | Var v -> v.var_id
        | Meta v -> v.meta_var.var_id
        | App (f, tys, args) -> (* TODO: Better combinator ? *)
                Hashtbl.hash (f.var_id :: List.rev_append
                    (List.rev_map get_ty_hash tys)
                    (List.rev_map get_term_hash args))
    in
    t.t_hash <- h

and get_term_hash t =
    if t.t_hash = -1 then hash_term t;
    assert (t.t_hash >= 0);
    t.t_hash

let h_eq    = 1
let h_pred  = 1
let h_not   = 1
let h_and   = 1
let h_or    = 1
let h_imply = 1
let h_equiv = 1
let h_all   = 1
let h_allty = 1
let h_ex    = 1

let rec hash_formula f =
    let aux h_skel l = Hashtbl.hash (h_skel, l) in
    let h = match f.formula with
        | Equal (t1, t2) -> aux h_eq [get_term_hash t1; get_term_hash t2]
        | Pred t -> aux h_pred (get_term_hash t)
        | Not f -> aux h_not (get_formula_hash f)
        | And l -> aux h_and (List.map get_formula_hash l)
        | Or l -> aux h_or (List.map get_formula_hash l)
        | Imply (f1, f2) -> aux h_imply [get_formula_hash f1; get_formula_hash f2]
        | Equiv (f1, f2) -> aux h_equiv [get_formula_hash f1; get_formula_hash f2]
        | All (l, f) -> aux h_all (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
        | AllTy (l, f) -> aux h_allty (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
        | Ex (l, f) -> aux h_ex (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    in
    f.f_hash <- h

and get_formula_hash f =
    if f.f_hash = -1 then hash_formula f;
    assert (f.f_hash >= 0);
    f.f_hash

(* Comparisons *)
(* ************************************************************************ *)

(* Lexicographic order on lists *)
let rec lexico compare l1 l2 = match l1, l2 with
    | [], [] -> 0
    | a :: r, b :: s ->
        begin match compare a b with
        | 0 -> lexico compare r s
        | x -> x
        end
    | [], _ -> -1
    | _, [] -> 1

(* Variables *)
let compare_var: 'a. 'a var -> 'a var -> int =
    fun v1 v2 -> Pervasives.compare v1.var_id v2.var_id

let equal_var v1 v2 = compare_var v1 v2 = 0

(* Types *)
let ty_discr ty = match ty.ty with
    | TyVar _ -> 1
    | TyMeta _ -> 2
    | TyApp _ -> 3

let rec compare_ty u v =
    let hu = get_ty_hash u and hv = get_ty_hash v in
    if hu <> hv then Pervasives.compare hu hv
    else match u.ty, v.ty with
    | TyVar v1, TyVar v2 -> compare_var v1 v2
    | TyMeta v1, TyMeta v2 -> compare_var v1.meta_var v2.meta_var
    | TyApp (f1, args1), TyApp (f2, args2) ->
        begin match compare_var f1 f2 with
        | 0 -> lexico compare_ty args1 args2
        | x -> x
        end
    | _, _ -> Pervasives.compare (ty_discr u) (ty_discr v)

let equal_ty u v =
    u == v || (get_ty_hash u = get_ty_hash v && compare_ty u v = 0)

(* Terms *)
let term_discr t = match t.term with
    | Var _ -> 1
    | Meta _ -> 2
    | App _ -> 3

let rec compare_term u v =
    let hu = get_term_hash u and hv = get_term_hash v in
    if hu <> hv then Pervasives.compare hu hv
    else match u.term, v.term with
    | Var v1, Var v2 -> compare_var v1 v2
    | Meta v1, Meta v2 -> compare_var v1.meta_var v2.meta_var
    | App (f1, tys1, args1), App (f2, tys2, args2) ->
        begin match compare_var f1 f2 with
        | 0 ->
                begin match lexico compare_ty tys1 tys2 with
                | 0 -> lexico compare_term args1 args2
                | x -> x
                end
        | x -> x
        end
    | _, _ -> Pervasives.compare (term_discr u) (term_discr v)

let equal_term u v =
    u == v || (get_term_hash u = get_term_hash v && compare_term u v = 0)

(* Formulas *)
let formula_discr f = match f.formula with
    | Equal _ -> 0
    | Pred _ -> 1
    | Not _ -> 2
    | And _ -> 3
    | Or _ -> 4
    | Imply _ -> 5
    | Equiv _ -> 6
    | All _ -> 7
    | AllTy _ -> 8
    | Ex _ -> 9

let rec compare_formula f g =
    let hf = get_formula_hash f and hg = get_formula_hash g in
    if hf <> hg then Pervasives.compare hf hg
    else match f.formula, g.formula with
    | Equal (u1, v1), Equal(u2, v2) -> lexico compare_term [u1; v1] [u2; v2]
    | Pred t1, Pred t2 -> compare_term t1 t2
    | Not h1, Not h2 -> compare_formula h1 h2
    | And l1, And l2 -> lexico compare_formula l1 l2
    | Or l1, Or l2 -> lexico compare_formula l1 l2
    | Imply (h1, i1), Imply (h2, i2) -> lexico compare_formula [h1; i1] [h2; i2]
    | Equiv (h1, i1), Equiv (h2, i2) -> lexico compare_formula [h1; i1] [h2; i2]
    | All (l1, h1), All (l2, h2) ->
            begin match lexico compare_var l1 l2 with
            | 0 -> compare_formula h1 h2
            | x -> x
            end
    | AllTy (l1, h1), AllTy (l2, h2) ->
            begin match lexico compare_var l1 l2 with
            | 0 -> compare_formula h1 h2
            | x -> x
            end
    | Ex (l1, h1), Ex (l2, h2) ->
            begin match lexico compare_var l1 l2 with
            | 0 -> compare_formula h1 h2
            | x -> x
            end
    | _, _ -> Pervasives.compare (formula_discr f) (formula_discr g)

let equal_formula u v =
    u == v || (get_formula_hash u = get_formula_hash v && compare_formula u v = 0)

(* Substitutions *)
(* ************************************************************************ *)

(*
module IntMap = Map.Make(struct
    type t = int
    let compare (i:int) j = Pervasives.compare i j
end)

(* map var.var_id to some 'a *)
type 'a subst = 'a IntMap.t

*)
