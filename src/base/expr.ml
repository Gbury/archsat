
(* Type definitions *)
(* ************************************************************************ *)

(* Variables, parametrized by the kind of the type of the variable *)
type 'ty var = {
  var_name : string;
  var_id : int; (** unique *)
  var_type : 'ty;
}

type 'ty meta = {
  meta_var : 'ty var;
  meta_index : int;
  meta_level : int;
}

type 'ty tau = {
  tau_var : 'ty var;
  tau_index : int;
}

(* Type for first order types *)
type ttype = Type

type 'ty function_descr = {
  fun_vars : ttype var list; (* prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

type ty_descr =
  | TyVar of ttype var
  | TyMeta of ttype meta
  | TyApp of ttype function_descr var * ty list

and ty = {
  ty : ty_descr;
  mutable ty_hash : int;
}

(* Terms & formulas *)
type term_descr =
  | Var of ty var
  | Meta of ty meta
  | Tau of ty tau
  | App of ty function_descr var * ty list * term list

and term = {
  term    : term_descr;
  t_type  : ty;
  mutable t_hash : int; (* lazy hash *)
}

and formula_descr =
  (* Atoms *)
  | Equal of term * term (* + ty ? *)
  | Pred of term

  (* Prop constructors *)
  | True
  | False
  | Not of formula
  | And of formula list
  | Or of formula list
  | Imply of formula * formula
  | Equiv of formula * formula

  (* Quantifiers *)
  | All of ty var list * formula
  | AllTy of ttype var list * formula
  | Ex of ty var list * formula
  | ExTy of ttype var list * formula

and formula = {
  formula : formula_descr;
  mutable f_hash  : int; (* lazy hash *)
}

(* Exceptions *)
(* ************************************************************************ *)

exception Type_error_doublon of string * int
exception Type_error_app of ty function_descr var * ty list * term list
exception Type_error_ty_app of ttype function_descr var * ty list
exception Type_error_mismatch of ty * ty

exception Cannot_assign of term
exception Cannot_interpret of term

exception Subst_error_ty_scope of ttype var
exception Subst_error_term_scope of ty var

(* Debug printing functions *)
(* ************************************************************************ *)

let debug_var b v = Printf.bprintf b "%s" v.var_name

let debug_meta b m = Printf.bprintf b "m%d_%a" m.meta_index debug_var m.meta_var

let debug_tau b t = Printf.bprintf b "t%d_%a" t.tau_index debug_var t.tau_var

let debug_ttype b = function Type -> Printf.bprintf b "$tType"

let rec debug_ty b ty = match ty.ty with
  | TyVar v -> debug_var b v
  | TyMeta m -> debug_meta b m
  | TyApp (f, []) ->
    Printf.bprintf b "%a" debug_var f
  | TyApp (f, l) ->
    Printf.bprintf b "%a(%a)" debug_var f (Util.pp_list ~sep:", " debug_ty) l

let debug_params b = function
    | [] -> ()
    | l -> Printf.bprintf b "∀ %a. " (Util.pp_list ~sep:", " debug_var) l

let debug_sig print b f =
    match f.fun_args with
    | [] -> Printf.bprintf b "%a%a" debug_params f.fun_vars print f.fun_ret
    | l -> Printf.bprintf b "%a%a -> %a" debug_params f.fun_vars
        (Util.pp_list ~sep:" -> " print) l print f.fun_ret

let debug_fun_ty = debug_sig debug_ty
let debug_fun_ttype = debug_sig debug_ttype

let debug_var_type debug b v = Printf.bprintf b "%a : %a" debug_var v debug v.var_type

let debug_var_ty = debug_var_type debug_ty
let debug_var_ttype = debug_var_type debug_ttype
let debug_const_ty = debug_var_type debug_fun_ty
let debug_const_ttype = debug_var_type debug_fun_ttype

let rec debug_term b t = match t.term with
  | Var v -> debug_var b v
  | Meta m -> debug_meta b m
  | Tau t -> debug_tau b t
  | App (f, [], []) ->
    Printf.bprintf b "%a" debug_var f
  | App (f, [], args) ->
    Printf.bprintf b "%a(%a)" debug_var f
      (Util.pp_list ~sep:", " debug_term) args
  | App (f, tys, args) ->
    Printf.bprintf b "%a(%a; %a)" debug_var f
      (Util.pp_list ~sep:", " debug_ty) tys
      (Util.pp_list ~sep:", " debug_term) args

let rec debug_formula b f =
  let aux b f = match f.formula with
    | Equal _ | Pred _ | True | False -> debug_formula b f
    | _ -> Printf.bprintf b "(%a)" debug_formula f
  in
  match f.formula with
  | Equal (x, y) -> Printf.bprintf b "%a = %a" debug_term x debug_term y
  | Pred t -> Printf.bprintf b "%a" debug_term t
  | True -> Printf.bprintf b "⊤"
  | False -> Printf.bprintf b "⊥"
  | Not f -> Printf.bprintf b "¬ %a" aux f
  | And l -> Printf.bprintf b "%a" (Util.pp_list ~sep:" ∧ " aux) l
  | Or l -> Printf.bprintf b "%a" (Util.pp_list ~sep:" ∨ " aux) l
  | Imply (p, q) -> Printf.bprintf b "%a ⇒ %a" aux p aux q
  | Equiv (p, q) -> Printf.bprintf b "%a ⇔ %a" aux p aux q
  | All (l, f) -> Printf.bprintf b "∀ %a. %a"
                    (Util.pp_list ~sep:", " debug_var_ty) l debug_formula f
  | AllTy (l, f) -> Printf.bprintf b "∀ %a. %a"
                      (Util.pp_list ~sep:", " debug_var_ttype) l debug_formula f
  | Ex (l, f) -> Printf.bprintf b "∃ %a. %a"
                   (Util.pp_list ~sep:", " debug_var_ty) l debug_formula f
  | ExTy (l, f) -> Printf.bprintf b "∃ %a. %a"
                   (Util.pp_list ~sep:", " debug_var_ttype) l debug_formula f

(* Printing functions *)
(* ************************************************************************ *)

let rec print_list f sep fmt = function
  | [] -> ()
  | [x] -> f fmt x
  | x :: ((y :: _) as r) ->
    Format.fprintf fmt "%a%s" f x sep;
    print_list f sep fmt r

let print_var fmt v = Format.fprintf fmt "%s" v.var_name

let print_meta fmt m = Format.fprintf fmt "m%d_%a" m.meta_index print_var m.meta_var

let print_tau fmt t = Format.fprintf fmt "t%d_%a" t.tau_index print_var t.tau_var

let print_ttype fmt = function Type -> Format.fprintf fmt "Type"

let rec print_ty fmt ty = match ty.ty with
  | TyVar v -> print_var fmt v
  | TyMeta m -> print_meta fmt m
  | TyApp (f, []) ->
    Format.fprintf fmt "%a" print_var f
  | TyApp (f, l) ->
    Format.fprintf fmt "%a(%a)" print_var f (print_list print_ty ", ") l

let print_var_ttype fmt v = Format.fprintf fmt "%a : %a" print_var v print_ttype v.var_type
let print_var_ty fmt v = Format.fprintf fmt "%a : %a" print_var v print_ty v.var_type

let rec print_term fmt t = match t.term with
  | Var v -> print_var fmt v
  | Meta m -> print_meta fmt m
  | Tau t -> print_tau fmt t
  | App (f, [], []) ->
    Format.fprintf fmt "%a" print_var f
  | App (f, [], args) ->
    Format.fprintf fmt "%a(%a)" print_var f
      (print_list print_term ", ") args
  | App (f, tys, args) ->
    Format.fprintf fmt "%a(%a; %a)" print_var f
      (print_list print_ty ", ") tys
      (print_list print_term ", ") args

let rec print_f fmt f =
  let aux fmt f = match f.formula with
    | Equal _ | Pred _ | True | False -> print_f fmt f
    | _ -> Format.fprintf fmt "(%a)" print_f f
  in
  match f.formula with
    | Equal (a, b) -> Format.fprintf fmt "%a = %a" print_term a print_term b
    | Pred t -> Format.fprintf fmt "%a" print_term t
    | True -> Format.fprintf fmt "⊤"
    | False -> Format.fprintf fmt "⊥"
    | Not f -> Format.fprintf fmt "¬ %a" aux f
    | And l -> Format.fprintf fmt "%a" (print_list aux " ∧ ") l
    | Or l -> Format.fprintf fmt "%a" (print_list aux " ∨ ") l
    | Imply (p, q) -> Format.fprintf fmt "%a ⇒ %a" aux p aux q
    | Equiv (p, q) -> Format.fprintf fmt "%a ⇔ %a" aux p aux q
    | All (l, f) -> Format.fprintf fmt "∀ %a. %a"
                      (print_list print_var_ty ", ") l print_f f
    | AllTy (l, f) -> Format.fprintf fmt "∀ %a. %a"
                        (print_list print_var_ttype ", ") l print_f f
    | Ex (l, f) -> Format.fprintf fmt "∃ %a. %a"
                     (print_list print_var_ty ", ") l print_f f
    | ExTy (l, f) -> Format.fprintf fmt "∃ %a. %a"
                       (print_list print_var_ttype ", ") l print_f f

let print_formula fmt f = Format.fprintf fmt "⟦%a⟧" print_f f

(* Hashs *)
(* ************************************************************************ *)

let hash h_skel l = Hashtbl.hash (h_skel, l)

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
    | Meta m -> m.meta_var.var_id
    | Tau t -> t.tau_var.var_id
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

(* TODO: FIXME *)
let h_eq    = 1
let h_pred  = 2
let h_true  = 3
let h_false = 4
let h_not   = 5
let h_and   = 6
let h_or    = 7
let h_imply = 8
let h_equiv = 9
let h_all   = 10
let h_allty = 11
let h_ex    = 12
let h_exty  = 13

let rec hash_formula f =
  let h = match f.formula with
    | Equal (t1, t2) -> hash h_eq [get_term_hash t1; get_term_hash t2]
    | Pred t -> hash h_pred (get_term_hash t)
    | True -> h_true
    | False -> h_false
    | Not f -> hash h_not (get_formula_hash f)
    | And l -> hash h_and (List.map get_formula_hash l)
    | Or l -> hash h_or (List.map get_formula_hash l)
    | Imply (f1, f2) -> hash h_imply [get_formula_hash f1; get_formula_hash f2]
    | Equiv (f1, f2) -> hash h_equiv [get_formula_hash f1; get_formula_hash f2]
    | All (l, f) -> hash h_all (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | AllTy (l, f) -> hash h_allty (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | Ex (l, f) -> hash h_ex (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | ExTy (l, f) -> hash h_exty (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
  in
  f.f_hash <- h

and get_formula_hash f =
  if f.f_hash = -1 then hash_formula f;
  assert (f.f_hash >= 0);
  f.f_hash

(* Comparisons *)
(* ************************************************************************ *)

(* Variables *)
let compare_var: 'a. 'a var -> 'a var -> int =
  fun v1 v2 -> Pervasives.compare v1.var_id v2.var_id

let compare_meta m1 m2 =
    match compare m1.meta_index m2.meta_index with
    | 0 -> compare_var m1.meta_var m2.meta_var
    | x -> x

let compare_tau t1 t2 =
    match compare t1.tau_index t2.tau_index with
    | 0 -> compare_var t1.tau_var t2.tau_var
    | x -> x

let equal_var v1 v2 = compare_var v1 v2 = 0
let equal_tau t1 t2 = compare_tau t1 t2 = 0
let equal_meta m1 m2 = compare_meta m1 m2 = 0

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
    | TyMeta m1, TyMeta m2 -> compare_meta m1 m2
    | TyApp (f1, args1), TyApp (f2, args2) ->
      begin match compare_var f1 f2 with
        | 0 -> Util.lexicograph compare_ty args1 args2
        | x -> x
      end
    | _, _ -> Pervasives.compare (ty_discr u) (ty_discr v)

let equal_ty u v =
  u == v || (get_ty_hash u = get_ty_hash v && compare_ty u v = 0)

(* Terms *)
let term_discr t = match t.term with
  | Var _ -> 1
  | Meta _ -> 2
  | Tau _ -> 3
  | App _ -> 4

let rec compare_term u v =
  let hu = get_term_hash u and hv = get_term_hash v in
  if hu <> hv then Pervasives.compare hu hv
  else match u.term, v.term with
    | Var v1, Var v2 -> compare_var v1 v2
    | Meta m1, Meta m2 -> compare_meta m1 m2
    | Tau t1, Tau t2 -> compare_tau t1 t2
    | App (f1, tys1, args1), App (f2, tys2, args2) ->
      begin match compare_var f1 f2 with
        | 0 ->
          begin match Util.lexicograph compare_ty tys1 tys2 with
            | 0 -> Util.lexicograph compare_term args1 args2
            | x -> x
          end
        | x -> x
      end
    | _, _ -> Pervasives.compare (term_discr u) (term_discr v)

let equal_term u v =
  u == v || (get_term_hash u = get_term_hash v && compare_term u v = 0)

(* Formulas *)
let formula_discr f = match f.formula with
  | Equal _ -> 1
  | Pred _ -> 2
  | True -> 3
  | False -> 4
  | Not _ -> 5
  | And _ -> 6
  | Or _ -> 7
  | Imply _ -> 8
  | Equiv _ -> 9
  | All _ -> 10
  | AllTy _ -> 11
  | Ex _ -> 12
  | ExTy _ -> 13

let rec compare_formula f g =
  let hf = get_formula_hash f and hg = get_formula_hash g in
  if hf <> hg then Pervasives.compare hf hg
  else match f.formula, g.formula with
    | True, True | False, False -> 0
    | Equal (u1, v1), Equal(u2, v2) -> Util.lexicograph compare_term [u1; v1] [u2; v2]
    | Pred t1, Pred t2 -> compare_term t1 t2
    | Not h1, Not h2 -> compare_formula h1 h2
    | And l1, And l2 -> Util.lexicograph compare_formula l1 l2
    | Or l1, Or l2 -> Util.lexicograph compare_formula l1 l2
    | Imply (h1, i1), Imply (h2, i2) -> Util.lexicograph compare_formula [h1; i1] [h2; i2]
    | Equiv (h1, i1), Equiv (h2, i2) -> Util.lexicograph compare_formula [h1; i1] [h2; i2]
    | All (l1, h1), All (l2, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | AllTy (l1, h1), AllTy (l2, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | Ex (l1, h1), Ex (l2, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | ExTy (l1, h1), ExTy (l2, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | _, _ -> Pervasives.compare (formula_discr f) (formula_discr g)

let equal_formula u v =
  u == v || (get_formula_hash u = get_formula_hash v && compare_formula u v = 0)

(* Module making *)
(* ************************************************************************ *)

module Subst = struct
  module Mi = Map.Make(struct type t = int let compare = Pervasives.compare end)

  type ('a, 'b) t = ('a * 'b) Mi.t

  let empty = Mi.empty

  let is_empty = Mi.is_empty

  let bind v t s = Mi.add v.var_id (v, t) s

  let remove v s = Mi.remove v.var_id s

  let get v s = snd (Mi.find v.var_id s)

  let iter f = Mi.iter (fun _ (v, t) -> f v t)
end

type ty_subst = (ttype var, ty) Subst.t
type term_subst = (ty var, term) Subst.t

module Hst = Hashtbl.Make(struct
    type t = string * ty
    let hash (s, ty) = Hashtbl.hash (s, get_ty_hash ty)
    let equal (s1, ty1) (s2, ty2) = s1 = s2 && equal_ty ty1 ty2
  end)

(* Interpreting and assigning *)
(* ************************************************************************ *)

type 't eval =
  | Interpreted of 't * int
  | Waiting of 't

let var_eval = Vector.make 107 None
let var_assign = Vector.make 107 None

let is_interpreted f =
  Vector.get var_eval f.var_id <> None

let interpreter v =
  match Vector.get var_eval v.var_id with
  | None -> raise Exit
  | Some (_, f) -> f

let eval t =
  try match t.term with
    | Var v -> (interpreter v) t
    | Meta m -> (interpreter m.meta_var) t
    | Tau e -> (interpreter e.tau_var) t
    | App (f, _, _) -> (interpreter f) t
  with Exit -> raise (Cannot_interpret t)

let is_assignable f =
  Vector.get var_assign f.var_id <> None

let assigner v =
  match Vector.get var_assign v.var_id with
  | None -> raise Exit
  | Some (_, f) -> f

let assign t =
  try match t.term with
    | Var v -> (assigner v) t
    | Meta m -> (assigner m.meta_var) t
    | Tau e -> (assigner e.tau_var) t
    | App (f, _, _) -> (assigner f) t
  with Exit -> raise (Cannot_assign t)

let set_eval v prio f =
  match Vector.get var_eval v.var_id with
  | None ->
    Vector.set var_eval v.var_id (Some (prio, f))
  | Some (i, _) when i < prio ->
    Vector.set var_eval v.var_id (Some (prio, f))
  | _ -> ()

let set_assign v prio f =
  match Vector.get var_assign v.var_id with
  | None ->
    Vector.set var_assign v.var_id (Some (prio, f))
  | Some (i, _) when i < prio ->
    Vector.set var_assign v.var_id (Some (prio, f))
  | _ -> ()

(* Variables constructors *)
(* ************************************************************************ *)

let n_var = ref ~-1
let mk_var name ty =
  incr n_var;
  Vector.push var_eval None;
  Vector.push var_assign None;
  { var_name = name; var_id = !n_var; var_type = ty; }

(* Variables are hashconsed, except for meta variables *)
let type_var_htbl : (string, ttype var) Hashtbl.t = Hashtbl.create 43
let type_const_htbl : (string, ttype function_descr var) Hashtbl.t = Hashtbl.create 43
let term_var_htbl : ty var Hst.t = Hst.create 43
let term_const_htbl : (string, ty function_descr var) Hashtbl.t = Hashtbl.create 43

let mk_ttype_var name =
  try Hashtbl.find type_var_htbl name
  with Not_found ->
    let res = mk_var name Type in
    Hashtbl.add type_var_htbl name res;
    res

let list_const n c =
  let rec aux acc n c =
    if n <= 0 then acc
    else aux (c :: acc) (n - 1) c
  in
  aux [] n c

let mk_ttype_fn_id name n =
  try Hashtbl.find type_const_htbl name
  with Not_found ->
    let res = mk_var name {
        fun_vars = [];
        fun_args = list_const n Type;
        fun_ret = Type;
      } in
    Hashtbl.add type_const_htbl name res;
    res

let mk_ty_var name ty =
  try Hst.find term_var_htbl (name, ty)
  with Not_found ->
    let res = mk_var name ty in
    Hst.add term_var_htbl (name, ty) res;
    res

let mk_ty_fn_id name tys args ret =
  try Hashtbl.find term_const_htbl name
  with Not_found ->
    let res = mk_var name {
        fun_vars = tys;
        fun_args = args;
        fun_ret = ret;
      } in
    Hashtbl.add term_const_htbl name res;
    res

(* Constructors for variables and constants *)
let ttype_var = mk_ttype_var
let ty_var = mk_ty_var
let type_const = mk_ttype_fn_id
let term_const = mk_ty_fn_id

(* Types & substitutions *)
(* ************************************************************************ *)

let mk_ty ty = { ty; ty_hash = -1 }

let type_var v = mk_ty (TyVar v)

let type_app f args =
  assert (f.var_type.fun_vars = []);
  if List.length args <> List.length f.var_type.fun_args then
    raise (Type_error_ty_app (f, args))
  else
    mk_ty (TyApp (f, args))

(* builtin prop type *)
let prop_cstr = type_const "Prop" 0
let type_prop = type_app prop_cstr []

(* substitutions *)
let rec type_subst_aux map t = match t.ty with
  | TyVar v -> begin try Subst.get v map with Not_found -> t end
  | TyMeta m -> begin try Subst.get m.meta_var map with Not_found -> t end
  | TyApp (f, args) -> type_app f (List.map (type_subst_aux map) args)

let type_subst map t = if Subst.is_empty map then t else type_subst_aux map t

(* typechecking *)
let type_inst f tys args =
  if List.length f.var_type.fun_vars <> List.length tys ||
     List.length f.var_type.fun_args <> List.length args then
    raise (Type_error_app (f, tys, args))
  else
    let map = List.fold_left (fun acc (v, ty) -> Subst.bind v ty acc) Subst.empty (List.combine f.var_type.fun_vars tys) in
    let fun_args = List.map (type_subst map) f.var_type.fun_args in
    if List.for_all2 equal_ty (List.map (fun x -> x.t_type) args) fun_args then
      type_subst map f.var_type.fun_ret
    else
      raise (Type_error_app (f, tys, args))

(* Terms & substitutions *)
(* ************************************************************************ *)

let mk_term t ty = {
  term = t;
  t_type = ty;
  t_hash = -1;
}

let term_var v =
  mk_term (Var v) v.var_type

let term_app f ty_args t_args =
  mk_term (App (f, ty_args, t_args)) (type_inst f ty_args t_args)

let rec term_subst_aux ty_map t_map t = match t.term with
  | Tau _ -> t
  | Var v ->
    begin try Subst.get v t_map with Not_found -> t end
  | Meta m ->
    begin try Subst.get m.meta_var t_map with Not_found -> t end
  | App (f, tys, args) ->
    term_app f (List.map (type_subst ty_map) tys) (List.map (term_subst_aux ty_map t_map) args)

let term_subst ty_map t_map t =
  if Subst.is_empty ty_map && Subst.is_empty t_map then t else term_subst_aux ty_map t_map t

(* Formulas & substitutions *)
(* ************************************************************************ *)

let mk_formula f = {formula = f; f_hash = -1; }

let f_equal a b =
  if not (equal_ty a.t_type b.t_type) then
    raise (Type_error_mismatch (a.t_type, b.t_type))
  else if (equal_ty type_prop a.t_type) then
    raise (Type_error_mismatch (type_prop, a.t_type))
  else if (equal_ty type_prop b.t_type) then
    raise (Type_error_mismatch (type_prop, b.t_type))
  else
  if compare_term a b < 0 then
    mk_formula (Equal (a, b))
  else
    mk_formula (Equal (b, a))

let f_pred t =
  if not (equal_ty type_prop t.t_type) then
    raise (Type_error_mismatch (type_prop, t.t_type))
  else
    mk_formula (Pred t)

let f_true = mk_formula True
let f_false = mk_formula False

let f_not f = match f.formula with
  | Not f' -> f'
  | _ -> mk_formula (Not f)

let f_and l =
  let rec aux acc = function
    | [] -> acc
    | { formula = And l' } :: r -> aux (List.rev_append l' acc) r
    | a :: r -> aux (a :: acc) r
  in
  match List.rev (aux [] l) with
  | [] -> f_false
  | l' -> mk_formula (And l')

let f_or l =
  let rec aux acc = function
    | [] -> acc
    | { formula = Or l' } :: r -> aux (List.rev_append l' acc) r
    | a :: r -> aux (a :: acc) r
  in
  match List.rev (aux [] l) with
  | [] -> f_true
  | l' -> mk_formula (Or l')

let f_imply p q = mk_formula (Imply (p, q))

let f_equiv p q = mk_formula (Equiv (p, q))

let f_all l f =
  if l = [] then f else
  let l, f = match f.formula with
    | All (l', f') -> l @ l', f'
    | _ -> l, f
  in
  mk_formula (All (l, f))

let f_allty l f =
  if l = [] then f else
  let l, f = match f.formula with
    | AllTy (l', f') -> l @ l', f'
    | _ -> l, f
  in
  mk_formula (AllTy (l, f))

let f_ex l f =
  if l = [] then f else
  let l, f = match f.formula with
    | Ex (l', f') -> l @ l', f'
    | _ -> l, f
  in
  mk_formula (Ex (l, f))

let f_exty l f =
  if l = [] then f else
  let l, f = match f.formula with
    | AllTy (l', f') -> l @ l', f'
    | _ -> l, f
  in
  mk_formula (ExTy (l, f))

let rec new_binder_subst ty_map subst acc = function
  | [] -> List.rev acc, subst
  | v :: r ->
    let ty = type_subst ty_map v.var_type in
    if not (equal_ty ty v.var_type) then
      let nv = ty_var v.var_name ty in
      new_binder_subst ty_map (Subst.bind v (term_var nv) subst) (nv :: acc) r
    else
      new_binder_subst ty_map (Subst.remove v subst) (v :: acc) r

(* TODO: Check free variables of substitutions for suantifiers ? *)
let rec formula_subst ty_map t_map f = match f.formula with
  | True | False -> f
  | Equal (a, b) -> f_equal (term_subst ty_map t_map a) (term_subst ty_map t_map b)
  | Pred t -> f_pred (term_subst ty_map t_map t)
  | Not f -> f_not (formula_subst ty_map t_map f)
  | And l -> f_and (List.map (formula_subst ty_map t_map) l)
  | Or l -> f_or (List.map (formula_subst ty_map t_map) l)
  | Imply (p, q) -> f_imply (formula_subst ty_map t_map p) (formula_subst ty_map t_map q)
  | Equiv (p, q) -> f_equiv (formula_subst ty_map t_map p) (formula_subst ty_map t_map q)
  | All (l, f) ->
    let l', t_map = new_binder_subst ty_map t_map [] l in
    Subst.iter (fun _ t -> match t.term with
        | Var v ->
          begin try raise (Subst_error_term_scope (List.find (equal_var v) l))
            with Not_found -> () end
        | _ -> ()
      ) t_map;
    f_all l' (formula_subst ty_map t_map f)
  | Ex (l, f) ->
    let l', t_map = new_binder_subst ty_map t_map [] l in
    Subst.iter (fun _ t -> match t.term with
        | Var v ->
          begin try raise (Subst_error_term_scope (List.find (equal_var v) l))
            with Not_found -> () end
        | _ -> ()
      ) t_map;
    f_ex l' (formula_subst ty_map t_map f)
  | AllTy (l, f) ->
    Subst.iter (fun _ ty -> match ty.ty with
        | TyVar v ->
          begin try raise (Subst_error_ty_scope (List.find (equal_var v) l))
            with Not_found -> () end
        | _ -> ()
      ) ty_map;
    f_allty l (formula_subst ty_map t_map f)
  | ExTy (l, f) ->
    Subst.iter (fun _ ty -> match ty.ty with
        | TyVar v ->
          begin try raise (Subst_error_ty_scope (List.find (equal_var v) l))
            with Not_found -> () end
        | _ -> ()
      ) ty_map;
    f_exty l (formula_subst ty_map t_map f)

(* Metas & Taus *)
(* ************************************************************************ *)

(* Metas/Taus refer to an index which stores the defining formula for the variable *)
let meta_ty_index = Vector.make 37 ({ formula = True; f_hash = -1 }, [])
let meta_term_index = Vector.make 37 ({ formula = True; f_hash = -1 }, [])
let tau_index = Vector.make 37 { formula = True; f_hash = -1 }

(* Metas *)
let mk_meta v i lvl = { meta_var = v; meta_index = i; meta_level = lvl; }

let get_meta_def i = fst (Vector.get meta_term_index i)
let get_meta_ty_def i = fst (Vector.get meta_ty_index i)

let ty_of_meta m = mk_ty (TyMeta m)
let term_of_meta m = mk_term (Meta m) m.meta_var.var_type

let mk_metas l f lvl =
  let i = Vector.size meta_term_index in
  let metas = List.map (fun v -> mk_meta v i lvl) l in
  Vector.push meta_term_index (f, metas);
  metas

let mk_ty_metas l f lvl =
  let i = Vector.size meta_ty_index in
  let metas = List.map (fun v -> mk_meta v i lvl) l in
  Vector.push meta_ty_index (f, metas);
  metas

let other_ty_metas m = snd (Vector.get meta_ty_index m.meta_index)
let other_term_metas m = snd (Vector.get meta_term_index m.meta_index)

let type_metas f lvl = match f.formula with
  | Not { formula = ExTy(l, _) } | AllTy (l, _) ->
    let new_vars = List.map (fun v -> mk_var v.var_name v.var_type) l in
    mk_ty_metas new_vars f lvl
  | _ -> invalid_arg "type_metas"

let term_metas f lvl = match f.formula with
  | Not { formula = Ex(l, _) } | All (l, _) ->
    let new_vars = List.map (fun v -> mk_var v.var_name v.var_type) l in
    mk_metas new_vars f lvl
  | _ -> invalid_arg "term_metas"

(* Taus *)
let mk_tau v i = { tau_var = v; tau_index = i }

let get_tau_def i = Vector.get tau_index i

let term_of_tau t = mk_term (Tau t) t.tau_var.var_type

let mk_taus l f =
  let i = Vector.size tau_index in
  Vector.push tau_index f;
  List.map (fun v -> mk_tau (mk_var v.var_name v.var_type) i) l

let term_taus f = match f.formula with
  | Not { formula = All (l, _) } | Ex (l, _) -> mk_taus l f
  | _ -> invalid_arg "type_metas"

(* Modules for simpler function names *)
(* ************************************************************************ *)

module Var = struct
  type 'a t = 'a var
  let hash v = v.var_id
  let compare = compare_var
  let equal = equal_var
  let print = print_var
  let debug = debug_var
end
module Meta = struct
  type 'a t = 'a meta
  let hash m = m.meta_var.var_id
  let compare = compare_meta
  let equal = equal_meta
  let print = print_meta
  let debug = debug_meta
end
module Tau = struct
  type 'a t = 'a tau
  let hash t = t.tau_var.var_id
  let compare = compare_tau
  let equal = equal_tau
  let print = print_tau
  let debug = debug_tau
end
module Ty = struct
  type t = ty
  let hash = get_ty_hash
  let compare = compare_ty
  let equal = equal_ty
  let print = print_ty
  let debug = debug_ty
end
module Term = struct
  type t = term
  let hash = get_term_hash
  let compare = compare_term
  let equal = equal_term
  let print = print_term
  let debug = debug_term
end
module Formula = struct
  type t = formula
  let hash = get_formula_hash
  let compare = compare_formula
  let equal = equal_formula
  let print = print_formula
  let debug = debug_formula
end

