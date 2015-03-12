
(* Type definitions *)
(* ************************************************************************ *)

(* Private aliases *)
type var_id = int
type 'a meta_index = int

(* Variables, parametrized by the kind of the type of the variable *)
type 'ty var = {
  var_name : string;
  var_id : var_id; (** unique *)
  var_type : 'ty;
}

type 'ty meta = {
  meta_var : 'ty var;
  meta_index : 'ty meta_index;
  can_unify : bool;
}

(* Type for first order types *)
type ttype = Type

type 'ty function_descr = {
  fun_vars : ttype var list; (* prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

type ty_descr =
  | TyVar of ttype var (** Bound variables *)
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
  | App of ty function_descr var * ty list * term list

and term = {
  term    : term_descr;
  t_type  : ty;
  mutable t_hash : int; (* lazy hash *)
}

type free_vars = ty list * term list

type formula_descr =
  (* Atoms *)
  | Pred of term
  | Equal of term * term

  (* Prop constructors *)
  | True
  | False
  | Not of formula
  | And of formula list
  | Or of formula list
  | Imply of formula * formula
  | Equiv of formula * formula

  (* Quantifiers *) (** All variables must have different names *)
  | All of ty var list * free_vars * formula
  | AllTy of ttype var list * free_vars * formula
  | Ex of ty var list * free_vars * formula
  | ExTy of ttype var list * free_vars * formula

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
  | All (l, _, f) -> Printf.bprintf b "∀ %a. %a"
                       (Util.pp_list ~sep:", " debug_var_ty) l debug_formula f
  | AllTy (l, _, f) -> Printf.bprintf b "∀ %a. %a"
                         (Util.pp_list ~sep:", " debug_var_ttype) l debug_formula f
  | Ex (l, _, f) -> Printf.bprintf b "∃ %a. %a"
                      (Util.pp_list ~sep:", " debug_var_ty) l debug_formula f
  | ExTy (l, _, f) -> Printf.bprintf b "∃ %a. %a"
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
  | All (l, _, f) -> Format.fprintf fmt "∀ %a. %a"
                       (print_list print_var_ty ", ") l print_f f
  | AllTy (l, _, f) -> Format.fprintf fmt "∀ %a. %a"
                         (print_list print_var_ttype ", ") l print_f f
  | Ex (l, _, f) -> Format.fprintf fmt "∃ %a. %a"
                      (print_list print_var_ty ", ") l print_f f
  | ExTy (l, _, f) -> Format.fprintf fmt "∃ %a. %a"
                        (print_list print_var_ttype ", ") l print_f f

let print_formula fmt f = Format.fprintf fmt "⟦%a⟧" print_f f

(* Hashs *)
(* ************************************************************************ *)

let hash h_skel l = Hashtbl.hash (h_skel, l)

let hash_var v = v.var_id
let hash_meta m = m.meta_var.var_id

let rec hash_ty t =
  let h = match t.ty with
    | TyVar v -> hash_var v
    | TyMeta m -> hash_meta m
    | TyApp (f, args) ->
      hash f.var_id (List.rev_map get_ty_hash args)
  in
  t.ty_hash <- h

and get_ty_hash t =
  if t.ty_hash = -1 then hash_ty t;
  assert (t.ty_hash >= 0);
  t.ty_hash

let rec hash_term t =
  let h = match t.term with
    | Var v -> hash_var v
    | Meta m -> hash_meta m
    | App (f, tys, args) ->
      hash f.var_id (List.rev_append
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
    | True -> hash h_true []
    | False -> hash h_false []
    | Not f -> hash h_not (get_formula_hash f)
    | And l -> hash h_and (List.map get_formula_hash l)
    | Or l -> hash h_or (List.map get_formula_hash l)
    | Imply (f1, f2) -> hash h_imply [get_formula_hash f1; get_formula_hash f2]
    | Equiv (f1, f2) -> hash h_equiv [get_formula_hash f1; get_formula_hash f2]
    | All (l, _, f) -> hash h_all (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | AllTy (l, _, f) -> hash h_allty (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | Ex (l, _, f) -> hash h_ex (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
    | ExTy (l, _, f) -> hash h_exty (get_formula_hash f :: List.rev_map (fun v -> v.var_id) l)
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
  fun v1 v2 -> compare v1.var_id v2.var_id

let compare_meta m1 m2 =
  match compare m1.meta_index m2.meta_index with
  | 0 -> compare_var m1.meta_var m2.meta_var
  | x -> x

let equal_var v1 v2 = compare_var v1 v2 = 0
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
  | App _ -> 3

let rec compare_term u v =
  let hu = get_term_hash u and hv = get_term_hash v in
  if hu <> hv then Pervasives.compare hu hv
  else match u.term, v.term with
    | Var v1, Var v2 -> compare_var v1 v2
    | Meta m1, Meta m2 -> compare_meta m1 m2
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
    | All (l1, _, h1), All (l2, _, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | AllTy (l1, _, h1), AllTy (l2, _, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | Ex (l1, _, h1), Ex (l2, _, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | ExTy (l1, _, h1), ExTy (l2, _, h2) ->
      begin match Util.lexicograph compare_var l1 l2 with
        | 0 -> compare_formula h1 h2
        | x -> x
      end
    | _, _ -> Pervasives.compare (formula_discr f) (formula_discr g)

let equal_formula u v =
  u == v || (get_formula_hash u = get_formula_hash v && compare_formula u v = 0)

(* Substitutions *)
(* ************************************************************************ *)

module Subst = struct
  module Mi = Map.Make(struct
      type t = int * int
      let compare (a, b) (c, d) = match compare a c with 0 -> compare b d | x -> x
    end)

  type ('a, 'b) t = ('a * 'b) Mi.t

  let empty = Mi.empty

  let is_empty = Mi.is_empty

  let iter f = Mi.iter (fun _ (key, value) -> f key value)

  let fold f = Mi.fold (fun _ (key, value) acc -> f key value acc)

  let bindings s = Mi.fold (fun _ (key, value) acc -> (key, value) :: acc) s []

  let equal f = Mi.equal (fun (_, value1) (_, value2) -> f value1 value2)
  let compare f = Mi.compare (fun (_, value1) (_, value2) -> f value1 value2)
  let hash h s = Mi.fold (fun i (_, value) acc -> Hashtbl.hash (acc, i, h value)) s 1

  let choose m = snd (Mi.choose m)

  let exists pred s =
    try
      iter (fun m s -> if pred m s then raise Exit) s;
      false
    with Exit ->
      true

  let for_all pred s =
    try
      iter (fun m s -> if not (pred m s) then raise Exit) s;
      true
    with Exit ->
      false

  module type S = sig
    type 'a key
    val get : 'a key -> ('a key, 'b) t -> 'b
    val mem : 'a key -> ('a key, 'b) t -> bool
    val bind : 'a key -> 'b -> ('a key, 'b) t -> ('a key, 'b) t
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
  end

  (* Variable substitutions *)
  module Var = struct
    type 'a key = 'a var
    let tok v = (v.var_id, 0)
    let get v s = snd (Mi.find (tok v) s)
    let mem v s = Mi.mem (tok v) s
    let bind v t s = Mi.add (tok v) (v, t) s
    let remove v s = Mi.remove (tok v) s
  end

  (* Meta substitutions *)
  module Meta = struct
    type 'a key = 'a meta
    let tok m = (m.meta_var.var_id, m.meta_index)
    let get m s = snd (Mi.find (tok m) s)
    let mem m s = Mi.mem (tok m) s
    let bind m t s = Mi.add (tok m) (m, t) s
    let remove m s = Mi.remove (tok m) s
  end

end

type ty_subst = (ttype var, ty) Subst.t
type term_subst = (ty var, term) Subst.t

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

(*
let type_var_htbl : (string, ttype var) Hashtbl.t = Hashtbl.create 43
let term_var_htbl : ty var Hst.t = Hst.create 43

let mk_ttype_var name =
  try Hashtbl.find type_var_htbl name
  with Not_found ->
    let res = mk_var name Type in
    Hashtbl.add type_var_htbl name res;
    res

let mk_ty_var name ty =
  try Hst.find term_var_htbl (name, ty)
  with Not_found ->
    let res = mk_var name ty in
    Hst.add term_var_htbl (name, ty) res;
    res

let ttype_var = mk_ttype_var
let ty_var = mk_ty_var

let type_const_htbl : (string, ttype function_descr var) Hashtbl.t = Hashtbl.create 43
let term_const_htbl : (string, ty function_descr var) Hashtbl.t = Hashtbl.create 43

let mk_ttype_fn_id name n =
  try Hashtbl.find type_const_htbl name
  with Not_found ->
    let res = mk_var name {
        fun_vars = [];
        fun_args = Util.times n (fun () -> Type);
        fun_ret = Type;
      } in
    Hashtbl.add type_const_htbl name res;
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

let type_const = mk_ttype_fn_id
let term_const = mk_ty_fn_id
*)
let ttype_var name = mk_var name Type
let ty_var name ty = mk_var name ty

let const name tys args ret = mk_var name {
    fun_vars = tys;
    fun_args = args;
    fun_ret = ret;
  }
let type_const name n = const name [] (Util.times n (fun () -> Type)) Type
let term_const = const

(* Types & substitutions *)
(* ************************************************************************ *)

let mk_ty ty = { ty; ty_hash = -1 }

let type_var v = mk_ty (TyVar v)

let type_meta m = mk_ty (TyMeta m)

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
  | TyVar v -> begin try Subst.Var.get v map with Not_found -> t end
  | TyMeta m -> begin try Subst.Var.get m.meta_var map with Not_found -> t end
  | TyApp (f, args) -> type_app f (List.map (type_subst_aux map) args)

let type_subst map t = if Subst.is_empty map then t else type_subst_aux map t

(* typechecking *)
let type_inst f tys args =
  if List.length f.var_type.fun_vars <> List.length tys ||
     List.length f.var_type.fun_args <> List.length args then
    raise (Type_error_app (f, tys, args))
  else
    let map = List.fold_left (fun acc (v, ty) -> Subst.Var.bind v ty acc) Subst.empty (List.combine f.var_type.fun_vars tys) in
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

let term_meta m =
  mk_term (Meta m) m.meta_var.var_type

let term_app f ty_args t_args =
  mk_term (App (f, ty_args, t_args)) (type_inst f ty_args t_args)

let rec term_subst_aux ty_map t_map t = match t.term with
  | Var v ->
    begin try Subst.Var.get v t_map with Not_found -> t end
  | Meta m ->
    begin try Subst.Var.get m.meta_var t_map with Not_found -> t end
  | App (f, tys, args) ->
    term_app f (List.map (type_subst ty_map) tys) (List.map (term_subst_aux ty_map t_map) args)

let term_subst ty_map t_map t =
  if Subst.is_empty ty_map && Subst.is_empty t_map then t else term_subst_aux ty_map t_map t

let rec var_occurs var t = match t.term with
  | Var v | Meta { meta_var = v } -> equal_var var v
  | App (f, tys, args) -> List.exists (var_occurs var) args

(* Free variables *)
(* ************************************************************************ *)

let init_fv acc = acc (* all the work is done in merge_fv *)

let merge_fv (ty1, t1) (ty2, t2) =
  Util.list_merge compare_var ty1 ty2,
  Util.list_merge compare_var t1 t2

let remove_fv (ty1, t1) (ty2, t2) =
  List.filter (fun v -> not (Util.list_mem equal_var v ty2)) ty1,
  List.filter (fun v -> not (Util.list_mem equal_var v t2)) t1

let rec ty_free_vars acc ty = match ty.ty with
  | TyVar v -> merge_fv acc ([v], [])
  | TyMeta _ -> acc
  | TyApp (_, args) -> List.fold_left ty_free_vars acc args

let rec term_free_vars acc t = match t.term with
  | Var v -> merge_fv acc ([], [v])
  | Meta _ -> acc
  | App (_, tys, args) ->
    let acc' = List.fold_left ty_free_vars acc tys in
    List.fold_left term_free_vars acc' args

let rec formula_free_vars acc f = match f.formula with
  | Pred t -> init_fv (term_free_vars acc t)
  | Equal (a, b) -> init_fv (term_free_vars (term_free_vars acc a) b)
  | True | False -> acc
  | Not p -> formula_free_vars acc p
  | And l | Or l -> List.fold_left formula_free_vars acc l
  | Imply (p, q) | Equiv (p, q) -> formula_free_vars (formula_free_vars acc p) q
  | AllTy (l, _, p) | ExTy (l, _, p) -> remove_fv (formula_free_vars acc p) (l, [])
  | All (l, _, p) | Ex (l, _, p) -> remove_fv (formula_free_vars acc p) ([], l)

let ty_fv = ty_free_vars ([], [])
let term_fv = term_free_vars ([], [])
let formula_fv = formula_free_vars ([], [])

let to_free_vars (tys, ts) = List.map type_var tys, List.map term_var ts

(* Taus *)
(* ************************************************************************ *)

let ty_taus = Hashtbl.create 17
let term_taus = Hashtbl.create 37

let get_ty_skolem v = Hashtbl.find ty_taus v.var_id
let get_term_skolem v = Hashtbl.find term_taus v.var_id

let init_ty_skolem v n =
  if not (Hashtbl.mem ty_taus v.var_id) then begin
    let res = type_const ("sk_" ^ v.var_name) n in
    Hashtbl.add ty_taus v.var_id res
  end

let init_term_skolem v tys args ret =
  if not (Hashtbl.mem term_taus v.var_id) then begin
    let res = term_const ("sk_" ^ v.var_name) tys args ret in
    Hashtbl.add term_taus v.var_id res
  end

let init_ty_skolems l (ty_vars, t_vars) =
  assert (t_vars = []); (* Else we would have dependent types *)
  let n = List.length ty_vars in
  List.iter (fun v -> init_ty_skolem v n) l

let init_term_skolems l (ty_vars, t_vars) =
  let args_types = List.map (fun v -> v.var_type) t_vars in
  List.iter (fun v -> init_term_skolem v ty_vars args_types v.var_type) l

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
  | True -> f_false
  | False -> f_true
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
      | All (l', _, f') -> l @ l', f'
      | _ -> l, f
    in
    let fv = formula_fv (mk_formula (All (l, ([], []), f))) in
    init_term_skolems l fv;
    mk_formula (All (l, to_free_vars fv, f))

let f_allty l f =
  if l = [] then f else
    let l, f = match f.formula with
      | AllTy (l', _, f') -> l @ l', f'
      | _ -> l, f
    in
    let fv = formula_fv (mk_formula (AllTy (l, ([], []), f))) in
    init_ty_skolems l fv;
    mk_formula (AllTy (l, to_free_vars fv, f))

let f_ex l f =
  if l = [] then f else
    let l, f = match f.formula with
      | Ex (l', _, f') -> l @ l', f'
      | _ -> l, f
    in
    let fv = formula_fv (mk_formula (Ex (l, ([], []), f))) in
    init_term_skolems l fv;
    mk_formula (Ex (l, to_free_vars fv, f))

let f_exty l f =
  if l = [] then f else
    let l, f = match f.formula with
      | AllTy (l', _, f') -> l @ l', f'
      | _ -> l, f
    in
    let fv = formula_fv (mk_formula (ExTy (l, ([], []), f))) in
    init_ty_skolems l fv;
    mk_formula (ExTy (l, to_free_vars fv, f))

let rec new_binder_subst ty_map subst acc = function
  | [] -> List.rev acc, subst
  | v :: r ->
    let ty = type_subst ty_map v.var_type in
    if not (equal_ty ty v.var_type) then
      let nv = ty_var v.var_name ty in
      new_binder_subst ty_map (Subst.Var.bind v (term_var nv) subst) (nv :: acc) r
    else
      new_binder_subst ty_map (Subst.Var.remove v subst) (v :: acc) r

(* TODO: Check free variables of substitutions for quantifiers ? *)
let rec formula_subst ty_map t_map f =
  match f.formula with
  | True | False -> f
  | Equal (a, b) -> f_equal (term_subst ty_map t_map a) (term_subst ty_map t_map b)
  | Pred t -> f_pred (term_subst ty_map t_map t)
  | Not f -> f_not (formula_subst ty_map t_map f)
  | And l -> f_and (List.map (formula_subst ty_map t_map) l)
  | Or l -> f_or (List.map (formula_subst ty_map t_map) l)
  | Imply (p, q) -> f_imply (formula_subst ty_map t_map p) (formula_subst ty_map t_map q)
  | Equiv (p, q) -> f_equiv (formula_subst ty_map t_map p) (formula_subst ty_map t_map q)
  | All (l, (ty, t), p) ->
    let l', t_map = new_binder_subst ty_map t_map [] l in
    let tys = List.map (type_subst ty_map) ty in
    let ts = List.map (term_subst ty_map t_map) t in
    mk_formula (All (l', (tys, ts), (formula_subst ty_map t_map p)))
  | Ex (l, (ty, t), p) ->
    let l', t_map = new_binder_subst ty_map t_map [] l in
    let tys = List.map (type_subst ty_map) ty in
    let ts = List.map (term_subst ty_map t_map) t in
    mk_formula (Ex (l', (tys, ts), (formula_subst ty_map t_map p)))
  | AllTy (l, (ty, t), p) ->
    assert (t = []);
    let tys = List.map (type_subst ty_map) ty in
    mk_formula (AllTy (l, (tys, t), (formula_subst ty_map t_map p)))
  | ExTy (l, (ty, t), p) ->
    assert (t = []);
    let tys = List.map (type_subst ty_map) ty in
    mk_formula (ExTy (l, (tys, t), (formula_subst ty_map t_map p)))

let formula_subst ty_map t_map f =
  Subst.iter (fun _ ty -> match ty.ty with TyVar _ -> assert false | _ -> ()) ty_map;
  Subst.iter (fun _ t -> match t.term with Var _ -> assert false | _ -> ()) t_map;
  if Subst.is_empty ty_map && Subst.is_empty t_map then f
  else formula_subst ty_map t_map f

let partial_inst ty_map t_map f = match f.formula with
  | All (l, args, p) ->
    let l' = List.filter (fun v -> not (Subst.Var.mem v t_map)) l in
    let q = formula_subst ty_map t_map p in
    if l' = [] then q else mk_formula (All (l', args, q))
  | AllTy (l, args, p) ->
    let l' = List.filter (fun v -> not (Subst.Var.mem v ty_map)) l in
    let q = formula_subst ty_map t_map p in
    if l' = [] then q else mk_formula (AllTy (l', args, q))
  | Not { formula = Ex (l, args, p) } ->
    let l' = List.filter (fun v -> not (Subst.Var.mem v t_map)) l in
    let q = formula_subst ty_map t_map p in
    f_not (if l' = [] then q else mk_formula (Ex (l', args, q)))
  | Not { formula = ExTy (l, args, p) } ->
    let l' = List.filter (fun v -> not (Subst.Var.mem v ty_map)) l in
    let q = formula_subst ty_map t_map p in
    f_not (if l' = [] then q else mk_formula (ExTy (l', args, q)))
  | _ -> f

(* Metas *)
(* ************************************************************************ *)

(* Metas refer to an index which stores the defining formula for the variable *)
let meta_ty_index = Vector.make 37 ({ formula = True; f_hash = -1 }, [])
let meta_term_index = Vector.make 37 ({ formula = True; f_hash = -1 }, [])

(* Metas *)
let mk_meta v i = {
  meta_var = v;
  meta_index = i;
  can_unify = true;
}

let protect meta = { meta with can_unify = false }

let get_meta_def i = fst (Vector.get meta_term_index i)
let get_meta_ty_def i = fst (Vector.get meta_ty_index i)

let mk_metas l f =
  let i = Vector.size meta_term_index in
  let metas = List.map (fun v -> mk_meta v i) l in
  Vector.push meta_term_index (f, metas);
  metas

let mk_ty_metas l f =
  let i = Vector.size meta_ty_index in
  let metas = List.map (fun v -> mk_meta v i) l in
  Vector.push meta_ty_index (f, metas);
  metas

let ty_metas_of_index i = snd (Vector.get meta_ty_index i)
let term_metas_of_index i = snd (Vector.get meta_term_index i)

let new_ty_metas f = match f.formula with
  | Not { formula = ExTy(l, _, _) } | AllTy (l, _, _) -> mk_ty_metas l f
  | _ -> invalid_arg "new_ty_metas"

let new_term_metas f = match f.formula with
  | Not { formula = Ex(l, _, _) } | All (l, _, _) -> mk_metas l f
  | _ -> invalid_arg "new_term_metas"

(* Modules for simpler function names *)
(* ************************************************************************ *)

module Var = struct
  type 'a t = 'a var
  let hash = hash_var
  let compare = compare_var
  let equal = equal_var
  let print = print_var
  let debug = debug_var
end
module Meta = struct
  type 'a t = 'a meta
  let hash = hash_meta
  let compare = compare_meta
  let equal = equal_meta
  let print = print_meta
  let debug = debug_meta
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

