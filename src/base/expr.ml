(*
   Base modules that defines the terms used in the prover.
*)

(* Type definitions *)
(* ************************************************************************ *)

(* Type for meta-variable multiplicity *)
type multiplicity =
  | Linear (* var should only be instantied once *)
  | Infinite (* you can do what you want *)

(* Type for evaluation result (not yet used) *)
type 't eval =
  | Interpreted of 't * int
  | Waiting of 't

(* Private aliases *)
type hash = int
type index = int
type status = int
type tag_map = Tag.map

type 'a tag = 'a Tag.t
type 'a meta_index = int

(* Extensible variant type for builtin operations *)
type builtin = ..
type builtin += Base

(* Identifiers, parametrized by the kind of the type of the variable *)
type 'ty id = {
  id_type : 'ty;
  id_name : string;
  index   : index; (** unique *)
  builtin : builtin;
}

(* Metavariables, basically, wrapped variables *)
type 'ty meta = {
  meta_id : 'ty id;
  meta_mult : multiplicity;
  meta_index : 'ty meta_index;
}

(* Type for first order types *)
type ttype = Type

(* The type of functions *)
type 'ty function_descr = {
  fun_vars : ttype id list; (* prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

(* Types *)
type ty_descr =
  | TyVar of ttype id (** Bound variables *)
  | TyMeta of ttype meta
  | TyApp of ttype function_descr id * ty list

and ty = {
  ty : ty_descr;
  ty_tags : tag_map;
  ty_status : status;
  mutable ty_hash : hash; (** lazy hash *)
}

(* Terms & formulas *)
type term_descr =
  | Var of ty id
  | Meta of ty meta
  | App of ty function_descr id * ty list * term list

and term = {
  term    : term_descr;
  t_type  : ty;
  t_tags : tag_map;
  t_status : status;
  mutable t_hash : hash; (* lazy hash *)
}

type free_args = ty list * term list

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
  | All of ty id list * free_args * formula
  | AllTy of ttype id list * free_args * formula
  | Ex of ty id list * free_args * formula
  | ExTy of ttype id list * free_args * formula

and formula = {
  f_tags : tag_map;
  formula : formula_descr;
  mutable f_hash  : hash; (* lazy hash *)
  mutable f_vars : (ttype id list * ty id list) option;
}

(* Exceptions *)
(* ************************************************************************ *)

exception Type_error_doublon of string * int
exception Type_error_app of ty function_descr id * ty list * term list
exception Type_error_ty_app of ttype function_descr id * ty list
exception Type_error_mismatch of ty * ty

exception Cannot_assign of term
exception Cannot_interpret of term

(* status settings *)
(* ************************************************************************ *)

module Status = struct
  let goal = 1
  let hypothesis = 0
end

(* Debug printing functions *)
(* ************************************************************************ *)

module Debug = struct
  let id b v = Printf.bprintf b "%s#%d" v.id_name v.index
  let meta b m = Printf.bprintf b "m%d_%a" m.meta_index id m.meta_id
  let ttype b Type = Printf.bprintf b "$tType"

  let rec ty b t = match t.ty with
    | TyVar v -> id b v
    | TyMeta m -> meta b m
    | TyApp (f, []) ->
      Printf.bprintf b "%a" id f
    | TyApp (f, l) ->
      Printf.bprintf b "%a(%a)" id f (CCPrint.list ~start:"" ~stop:"" ~sep:", " ty) l

  let params b = function
    | [] -> ()
    | l -> Printf.bprintf b "∀ %a. " (CCPrint.list ~start:""~stop:"" ~sep:", " id) l

  let signature print b f =
    match f.fun_args with
    | [] -> Printf.bprintf b "%a%a" params f.fun_vars print f.fun_ret
    | l -> Printf.bprintf b "%a%a -> %a" params f.fun_vars
             (CCPrint.list ~start:"" ~stop:"" ~sep:" -> " print) l print f.fun_ret

  let fun_ty = signature ty
  let fun_ttype = signature ttype

  let id_type debug b v = Printf.bprintf b "%a : %a" id v debug v.id_type

  let id_ty = id_type ty
  let id_ttype = id_type ttype
  let const_ty = id_type fun_ty
  let const_ttype = id_type fun_ttype

  let rec term b t = match t.term with
    | Var v -> id b v
    | Meta m -> meta b m
    | App (f, [], []) ->
      Printf.bprintf b "%a" id f
    | App (f, [], args) ->
      Printf.bprintf b "%a(%a)" id f
        (CCPrint.list ~start:"" ~stop:"" ~sep:", " term) args
    | App (f, tys, args) ->
      Printf.bprintf b "%a(%a; %a)" id f
        (CCPrint.list ~start:"" ~stop:"" ~sep:", " ty) tys
        (CCPrint.list ~start:"" ~stop:"" ~sep:", " term) args

  let rec formula b f =
    let aux b f = match f.formula with
      | Equal _ | Pred _ | True | False -> formula b f
      | _ -> Printf.bprintf b "(%a)" formula f
    in
    match f.formula with
    | Equal (x, y) -> Printf.bprintf b "%a = %a" term x term y
    | Pred t -> Printf.bprintf b "%a" term t
    | True -> Printf.bprintf b "⊤"
    | False -> Printf.bprintf b "⊥"
    | Not f -> Printf.bprintf b "¬ %a" aux f
    | And l -> Printf.bprintf b "%a" (CCPrint.list ~start:"" ~stop:"" ~sep:" ∧ " aux) l
    | Or l -> Printf.bprintf b "%a" (CCPrint.list ~start:"" ~stop:"" ~sep:" ∨ " aux) l
    | Imply (p, q) -> Printf.bprintf b "%a ⇒ %a" aux p aux q
    | Equiv (p, q) -> Printf.bprintf b "%a ⇔ %a" aux p aux q
    | All (l, _, f) -> Printf.bprintf b "∀ %a. %a"
                         (CCPrint.list ~start:"" ~stop:"" ~sep:", " id_ty) l formula f
    | AllTy (l, _, f) -> Printf.bprintf b "∀ %a. %a"
                           (CCPrint.list ~start:"" ~stop:"" ~sep:", " id_ttype) l formula f
    | Ex (l, _, f) -> Printf.bprintf b "∃ %a. %a"
                        (CCPrint.list ~start:"" ~stop:"" ~sep:", " id_ty) l formula f
    | ExTy (l, _, f) -> Printf.bprintf b "∃ %a. %a"
                          (CCPrint.list ~start:"" ~stop:"" ~sep:", " id_ttype) l formula f
end

(* Printing functions *)
(* ************************************************************************ *)

module Print = struct
  let rec list f sep fmt = function
    | [] -> ()
    | [x] -> f fmt x
    | x :: ((y :: _) as r) ->
      Format.fprintf fmt "%a%s" f x sep;
      list f sep fmt r

  let id fmt v = Format.fprintf fmt "%s" v.id_name

  let meta fmt m = Format.fprintf fmt "m%d_%a" m.meta_index id m.meta_id

  let ttype fmt = function Type -> Format.fprintf fmt "Type"

  let rec ty fmt t = match t.ty with
    | TyVar v -> id fmt v
    | TyMeta m -> meta fmt m
    | TyApp (f, []) ->
      Format.fprintf fmt "%a" id f
    | TyApp (f, l) ->
      Format.fprintf fmt "%a(%a)" id f (list ty ", ") l

  let id_ttype fmt v = Format.fprintf fmt "%a : %a" id v ttype v.id_type
  let id_ty fmt v = Format.fprintf fmt "%a : %a" id v ty v.id_type

  let rec term fmt t = match t.term with
    | Var v -> id fmt v
    | Meta m -> meta fmt m
    | App (f, [], []) ->
      Format.fprintf fmt "%a" id f
    | App (f, [], args) ->
      Format.fprintf fmt "%a(%a)" id f
        (list term ", ") args
    | App (f, tys, args) ->
      Format.fprintf fmt "%a(%a; %a)" id f
        (list ty ", ") tys
        (list term ", ") args

  let rec formula_aux fmt f =
    let aux fmt f = match f.formula with
      | Equal _ | Pred _ | True | False -> formula_aux fmt f
      | _ -> Format.fprintf fmt "(%a)" formula_aux f
    in
    match f.formula with
    | Equal (a, b) -> Format.fprintf fmt "%a = %a" term a term b
    | Pred t -> Format.fprintf fmt "%a" term t
    | True -> Format.fprintf fmt "⊤"
    | False -> Format.fprintf fmt "⊥"
    | Not f -> Format.fprintf fmt "¬ %a" aux f
    | And l -> Format.fprintf fmt "%a" (list aux " ∧ ") l
    | Or l -> Format.fprintf fmt "%a" (list aux " ∨ ") l
    | Imply (p, q) -> Format.fprintf fmt "%a ⇒ %a" aux p aux q
    | Equiv (p, q) -> Format.fprintf fmt "%a ⇔ %a" aux p aux q
    | All (l, _, f) -> Format.fprintf fmt "∀ %a. %a"
                         (list id_ty ", ") l formula_aux f
    | AllTy (l, _, f) -> Format.fprintf fmt "∀ %a. %a"
                           (list id_ttype ", ") l formula_aux f
    | Ex (l, _, f) -> Format.fprintf fmt "∃ %a. %a"
                        (list id_ty ", ") l formula_aux f
    | ExTy (l, _, f) -> Format.fprintf fmt "∃ %a. %a"
                          (list id_ttype ", ") l formula_aux f

  let formula fmt f = Format.fprintf fmt "⟦%a⟧" formula_aux f

end

(* Substitutions *)
(* ************************************************************************ *)

module Subst = struct
  module Mi = Map.Make(struct
      type t = int * int
      let compare (a, b) (c, d) = match compare a c with 0 -> compare b d | x -> x
    end)

  type ('a, 'b) t = ('a * 'b) Mi.t

  (* Usual functions *)
  let empty = Mi.empty

  let is_empty = Mi.is_empty

  let iter f = Mi.iter (fun _ (key, value) -> f key value)

  let fold f = Mi.fold (fun _ (key, value) acc -> f key value acc)

  let bindings s = Mi.fold (fun _ (key, value) acc -> (key, value) :: acc) s []

  (* Comparisons *)
  let equal f = Mi.equal (fun (_, value1) (_, value2) -> f value1 value2)
  let compare f = Mi.compare (fun (_, value1) (_, value2) -> f value1 value2)
  let hash h s = Mi.fold (fun i (_, value) acc -> Hashtbl.hash (acc, i, h value)) s 1

  let choose m = snd (Mi.choose m)

  (* Iterators *)
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

  let debug debug_key debug_value buf map =
    let aux _ (key, value) =
      Printf.bprintf buf "%a -> %a; " debug_key key debug_value value
    in
    Printf.bprintf buf "%a" (fun _ -> Mi.iter aux) map

  let print print_key print_value fmt map =
    let aux _ (key, value) =
      Format.fprintf fmt "%a -> %a@ " print_key key print_value value
    in
    Format.fprintf fmt "@[<hov 0>%a@]" (fun _ -> Mi.iter aux) map

  module type S = sig
    type 'a key
    val get : 'a key -> ('a key, 'b) t -> 'b
    val mem : 'a key -> ('a key, 'b) t -> bool
    val bind : 'a key -> 'b -> ('a key, 'b) t -> ('a key, 'b) t
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
  end

  (* Variable substitutions *)
  module Id = struct
    type 'a key = 'a id
    let tok v = (v.index, 0)
    let get v s = snd (Mi.find (tok v) s)
    let mem v s = Mi.mem (tok v) s
    let bind v t s = Mi.add (tok v) (v, t) s
    let remove v s = Mi.remove (tok v) s
  end

  (* Meta substitutions *)
  module Meta = struct
    type 'a key = 'a meta
    let tok m = (m.meta_id.index, m.meta_index)
    let get m s = snd (Mi.find (tok m) s)
    let mem m s = Mi.mem (tok m) s
    let bind m t s = Mi.add (tok m) (m, t) s
    let remove m s = Mi.remove (tok m) s
  end

end

(* Variables *)
(* ************************************************************************ *)

module Id = struct
  type 'a t = 'a id

  (* Hash & comparisons *)
  let hash_aux v = CCHash.int_ v.index
  let hash v = CCHash.apply hash_aux v

  let compare: 'a. 'a id -> 'a id -> int =
    fun v1 v2 -> compare v1.index v2.index

  let equal v1 v2 = compare v1 v2 = 0

  (* Printing functions *)
  let print = Print.id
  let debug = Debug.id

  (* Internal state *)
  let id_index = ref ~-1
  let eval_vec = CCVector.make 107 None
  let assign_vec = CCVector.make 107 None
  let ty_skolems = Hashtbl.create 17
  let term_skolems = Hashtbl.create 107

  (* Constructors *)
  let mk_new ?(builtin=Base) name ty =
    incr id_index;
    CCVector.push eval_vec None;
    CCVector.push assign_vec None;
    { id_name = name; index = !id_index; id_type = ty; builtin }

  let ttype ?builtin name = mk_new ?builtin name Type
  let ty ?builtin name ty = mk_new ?builtin name ty

  let const ?builtin name fun_vars fun_args fun_ret =
    mk_new ?builtin name { fun_vars; fun_args; fun_ret; }

  let ty_fun ?builtin name n = const ?builtin name [] (CCList.replicate n Type) Type
  let term_fun = const

  (* Builtin Prop Type *)
  let prop = ty_fun "Prop" 0

  (* Free variables *)
  let null_fv = [], []

  let merge_fv (ty1, t1) (ty2, t2) =
    CCList.sorted_merge_uniq ~cmp:compare ty1 ty2,
    CCList.sorted_merge_uniq ~cmp:compare t1 t2

  let remove_fv (ty1, t1) (ty2, t2) =
    List.filter (fun v -> not (CCList.Set.mem ~eq:equal v ty2)) ty1,
    List.filter (fun v -> not (CCList.Set.mem ~eq:equal v t2)) t1

  (* Variable occurs in a term *)
  let rec occurs_in_term var t = match t.term with
    | Var v | Meta { meta_id = v } -> equal var v
    | App (f, tys, args) -> List.exists (occurs_in_term var) args

  (* Evaluation *)
  let is_interpreted f =
    CCVector.get eval_vec f.index <> None

  let interpreter v =
    match CCVector.get eval_vec v.index with
    | None -> raise Exit
    | Some (_, f) -> f

  let set_eval v prio f =
    match CCVector.get eval_vec v.index with
    | None ->
      CCVector.set eval_vec v.index (Some (prio, f))
    | Some (i, _) when i < prio ->
      CCVector.set eval_vec v.index (Some (prio, f))
    | _ -> ()

  (* Assignments *)
  let is_assignable f =
    CCVector.get assign_vec f.index <> None

  let assigner v =
    match CCVector.get assign_vec v.index with
    | None -> raise Exit
    | Some (_, f) -> f

  let set_assign v prio f =
    match CCVector.get assign_vec v.index with
    | None ->
      CCVector.set assign_vec v.index (Some (prio, f))
    | Some (i, _) when i < prio ->
      CCVector.set assign_vec v.index (Some (prio, f))
    | _ -> ()

  (* Skolems symbols *)
  let ty_skolem v = Hashtbl.find ty_skolems v.index
  let term_skolem v = Hashtbl.find term_skolems v.index

  let init_ty_skolem v n =
    let res = ty_fun ("sk_" ^ v.id_name) n in
    Hashtbl.add ty_skolems v.index res

  let init_term_skolem v tys args ret =
    let res = term_fun ("sk_" ^ v.id_name) tys args ret in
    Hashtbl.add term_skolems v.index res

  let init_ty_skolems l (ty_vars, t_vars) =
    assert (t_vars = []); (* Else we would have dependent types *)
    let n = List.length ty_vars in
    List.iter (fun v -> init_ty_skolem v n) l

  let init_term_skolems l (ty_vars, t_vars) =
    let args_types = List.map (fun v -> v.id_type) t_vars in
    List.iter (fun v -> init_term_skolem v ty_vars args_types v.id_type) l

end

(* Meta-variables *)
(* ************************************************************************ *)

module Meta = struct
  type 'a t = 'a meta

  (* Hash & Comparisons *)
  let hash_aux m = CCHash.int_ m.meta_id.index
  let hash m = CCHash.apply hash_aux m

  let compare m1 m2 =
    match compare m1.meta_index m2.meta_index with
    | 0 -> Id.compare m1.meta_id m2.meta_id
    | x -> x

  let equal m1 m2 = compare m1 m2 = 0

  (* Printing functions *)
  let print = Print.meta
  let debug = Debug.meta

  (* Free meta-variables *)
  let merge_metas (ty1, t1) (ty2, t2) =
    CCList.sorted_merge_uniq ~cmp:compare ty1 ty2,
    CCList.sorted_merge_uniq ~cmp:compare t1 t2

  let rec ty_free_metas acc ty = match ty.ty with
    | TyVar _ -> acc
    | TyMeta m -> merge_metas acc ([m], [])
    | TyApp (_, args) -> List.fold_left ty_free_metas acc args

  let rec term_free_metas acc t = match t.term with
    | Var _ -> acc
    | Meta m -> merge_metas acc ([], [m])
    | App (_, tys, args) ->
      let acc' = List.fold_left ty_free_metas acc tys in
      List.fold_left term_free_metas acc' args

  let in_ty = ty_free_metas ([], [])
  let in_term = term_free_metas ([], [])

  (* Metas refer to an index which stores the defining formula for the variable *)
  let dummy_formula = { formula = True; f_hash = -1; f_vars = None; f_tags = Tag.empty; }
  let meta_ty_index = CCVector.make 37 (dummy_formula, [])
  let meta_term_index = CCVector.make 37 (dummy_formula, [])

  let rec mult_of_f f = match f.formula with
    | Pred _ | Equal _ -> Infinite
    | Not { formula = Ex (_, _, f') } | All (_, _, f')
    | Not { formula = ExTy (_, _, f') } | AllTy (_, _, f') ->
      mult_of_f f'
    | Not { formula = Imply (p, q) } ->
      if mult_of_f p = Infinite && mult_of_f q = Infinite then
        Infinite
      else Linear
    | Not { formula = Or l } | And l ->
      if List.for_all (fun f' -> mult_of_f f'  = Infinite) l then
        Infinite
      else
        Linear
    | _ -> Linear

  (* Metas *)
  let mk_meta v i m = {
    meta_id = v;
    meta_mult = m;
    meta_index = i;
  }

  let ty_def i = fst (CCVector.get meta_term_index i)
  let ttype_def i = fst (CCVector.get meta_ty_index i)

  let mk_metas l f =
    let i = CCVector.size meta_term_index in
    let metas = List.map (fun v -> mk_meta v i (mult_of_f f)) l in
    CCVector.push meta_term_index (f, metas);
    metas

  let mk_ty_metas l f =
    let i = CCVector.size meta_ty_index in
    let metas = List.map (fun v -> mk_meta v i (mult_of_f f)) l in
    CCVector.push meta_ty_index (f, metas);
    metas

  let of_ttype_index i = snd (CCVector.get meta_ty_index i)
  let of_ty_index i = snd (CCVector.get meta_term_index i)

  let of_all_ty f = match f.formula with
    | Not { formula = ExTy(l, _, _) } | AllTy (l, _, _) -> mk_ty_metas l f
    | _ -> invalid_arg "new_ty_metas"

  let of_all f = match f.formula with
    | Not { formula = Ex(l, _, _) } | All (l, _, _) -> mk_metas l f
    | _ -> invalid_arg "new_term_metas"

end

(* Types *)
(* ************************************************************************ *)

module Ty = struct
  type t = ty
  type subst = (ttype id, ty) Subst.t

  (* Hash & Comparisons *)
  let rec hash_aux t h = match t.ty with
    | TyVar v -> Id.hash_aux v h
    | TyMeta m -> Meta.hash_aux m h
    | TyApp (f, args) ->
      h |> Id.hash_aux f |> CCHash.(list_ int_) (List.map hash args)

  and hash t =
    if t.ty_hash = -1 then
      t.ty_hash <- CCHash.apply hash_aux t;
    t.ty_hash

  let discr ty = match ty.ty with
    | TyVar _ -> 1
    | TyMeta _ -> 2
    | TyApp _ -> 3

  let rec compare u v =
    let hu = hash u and hv = hash v in
    if hu <> hv then Pervasives.compare hu hv
    else match u.ty, v.ty with
      | TyVar v1, TyVar v2 -> Id.compare v1 v2
      | TyMeta m1, TyMeta m2 -> Meta.compare m1 m2
      | TyApp (f1, args1), TyApp (f2, args2) ->
        begin match Id.compare f1 f2 with
          | 0 -> Util.lexicograph compare args1 args2
          | x -> x
        end
      | _, _ -> Pervasives.compare (discr u) (discr v)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.ty
  let debug = Debug.ty
  let debug_subst = Subst.debug Debug.id Debug.ty

  (* Constructors *)
  let mk_ty ?(status=Status.hypothesis) ty =
    { ty; ty_status = status; ty_hash = -1; ty_tags = Tag.empty; }

  let of_id ?status v = mk_ty ?status (TyVar v)

  let of_meta ?status m = mk_ty ?status (TyMeta m)

  let apply ?status f args =
    assert (f.id_type.fun_vars = []);
    if List.length args <> List.length f.id_type.fun_args then
      raise (Type_error_ty_app (f, args))
    else
      mk_ty ?status (TyApp (f, args))

  (* Tags *)
  let get_tag ty k = Tag.get ty.ty_tags k
  let tag ty k v = { ty with ty_tags = Tag.add ty.ty_tags k v }

  (* Builtin Prop Type *)
  let prop = apply Id.prop []

  (* Substitutions *)
  let rec subst_aux map t = match t.ty with
    | TyVar v -> begin try Subst.Id.get v map with Not_found -> t end
    | TyMeta m -> begin try Subst.Id.get m.meta_id map with Not_found -> t end
    | TyApp (f, args) ->
      let new_args = List.map (subst_aux map) args in
      if List.for_all2 (==) args new_args then t
      else apply ~status:t.ty_status f new_args

  let subst map t = if Subst.is_empty map then t else subst_aux map t

  (* Typechecking *)
  let instantiate f tys args =
    if List.length f.id_type.fun_vars <> List.length tys ||
       List.length f.id_type.fun_args <> List.length args then
      raise (Type_error_app (f, tys, args))
    else
      let map = List.fold_left2 (fun acc v ty -> Subst.Id.bind v ty acc) Subst.empty f.id_type.fun_vars tys in
      let fun_args = List.map (subst map) f.id_type.fun_args in
      if List.for_all2 equal (List.map (fun x -> x.t_type) args) fun_args then
        subst map f.id_type.fun_ret
      else
        raise (Type_error_app (f, tys, args))

  (* Free variables *)
  let rec free_vars acc ty = match ty.ty with
    | TyVar v -> Id.merge_fv acc ([v], [])
    | TyMeta _ -> acc
    | TyApp (_, args) -> List.fold_left free_vars acc args

  let fv = free_vars Id.null_fv

end

(* Terms *)
(* ************************************************************************ *)

module Term = struct
  type t = term
  type subst = (ty id, term) Subst.t

  (* Hash & Comparisons *)
  let rec hash_aux t h = match t.term with
    | Var v -> Id.hash_aux v h
    | Meta m -> Meta.hash_aux m h
    | App (f, tys, args) ->
      h |> Id.hash_aux f
      |> CCHash.(list_ int_) (List.map Ty.hash tys)
      |> CCHash.(list_ int_) (List.map hash args)

  and hash t =
    if t.t_hash = -1 then
      t.t_hash <- CCHash.apply hash_aux t;
    t.t_hash

  let discr t = match t.term with
    | Var _ -> 1
    | Meta _ -> 2
    | App _ -> 3

  let rec compare u v =
    let hu = hash u and hv = hash v in
    if hu <> hv then Pervasives.compare hu hv
    else match u.term, v.term with
      | Var v1, Var v2 -> Id.compare v1 v2
      | Meta m1, Meta m2 -> Meta.compare m1 m2
      | App (f1, tys1, args1), App (f2, tys2, args2) ->
        begin match Id.compare f1 f2 with
          | 0 ->
            begin match Util.lexicograph Ty.compare tys1 tys2 with
              | 0 -> Util.lexicograph compare args1 args2
              | x -> x
            end
          | x -> x
        end
      | _, _ -> Pervasives.compare (discr u) (discr v)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.term
  let debug = Debug.term
  let debug_subst = Subst.debug Debug.id Debug.term

  (* Constructors *)
  let mk_term ?(status=Status.hypothesis) term t_type =
    { term; t_type; t_status = status; t_hash = -1; t_tags = Tag.empty }

  let of_id ?status v =
    mk_term ?status (Var v) v.id_type

  let of_meta ?status m =
    mk_term ?status (Meta m) m.meta_id.id_type

  let apply ?status f ty_args t_args =
    mk_term ?status (App (f, ty_args, t_args)) (Ty.instantiate f ty_args t_args)

  (* Tags *)
  let get_tag t k = Tag.get t.t_tags k
  let tag t k v = { t with t_tags = Tag.add t.t_tags k v }

  (* Substitutions *)
  let rec subst_aux ty_map t_map t = match t.term with
    | Var v -> begin try Subst.Id.get v t_map with Not_found -> t end
    | Meta m -> begin try Subst.Id.get m.meta_id t_map with Not_found -> t end
    | App (f, tys, args) ->
      let new_tys = List.map (Ty.subst ty_map) tys in
      let new_args = List.map (subst_aux ty_map t_map) args in
      if List.for_all2 (==) new_tys tys && List.for_all2 (==) new_args args then t
      else apply ~status:t.t_status f new_tys new_args

  let subst ty_map t_map t =
    if Subst.is_empty ty_map && Subst.is_empty t_map then
      t
    else
      subst_aux ty_map t_map t

  let rec replace (t, t') t'' = match t''.term with
    | _ when equal t t'' -> t'
    | App (f, ty_args, t_args) ->
      apply ~status:t''.t_status f ty_args (List.map (replace (t, t')) t_args)
    | _ -> t''

  (* Free variables *)
  let rec free_vars acc t = match t.term with
    | Var v -> Id.merge_fv acc ([], [v])
    | Meta _ -> acc
    | App (_, tys, args) ->
      let acc' = List.fold_left Ty.free_vars acc tys in
      List.fold_left free_vars acc' args

  let fv = free_vars Id.null_fv

  (* Evaluation & Assignment *)
  let eval t =
    try match t.term with
      | Var v -> (Id.interpreter v) t
      | Meta m -> (Id.interpreter m.meta_id) t
      | App (f, _, _) -> (Id.interpreter f) t
    with Exit -> raise (Cannot_interpret t)

  let assign t =
    try match t.term with
      | Var v -> (Id.assigner v) t
      | Meta m -> (Id.assigner m.meta_id) t
      | App (f, _, _) -> (Id.assigner f) t
    with Exit -> raise (Cannot_assign t)

end

(* Formulas *)
(* ************************************************************************ *)

module Formula = struct
  type t = formula

  (* Hash & Comparisons *)
  let h_eq    = 2
  let h_pred  = 3
  let h_true  = 5
  let h_false = 7
  let h_not   = 11
  let h_and   = 13
  let h_or    = 17
  let h_imply = 19
  let h_equiv = 23
  let h_all   = 29
  let h_allty = 31
  let h_ex    = 37
  let h_exty  = 41

  let rec hash_aux f h = match f.formula with
    | Equal (t1, t2) ->
      h |> CCHash.int_ h_eq |> CCHash.int_ (Term.hash t1) |> CCHash.int_ (Term.hash t2)
    | Pred t ->
      h |> CCHash.int_ h_pred |> CCHash.int_ (Term.hash t)
    | True ->
      h |> CCHash.int_ h_true
    | False ->
      h |> CCHash.int_ h_false
    | Not f ->
      h |> CCHash.int_ h_not |> CCHash.int_ (hash f)
    | And l ->
      h |> CCHash.int_ h_and |> CCHash.(list_ int_) (List.map hash l)
    | Or l ->
      h |> CCHash.int_ h_or |> CCHash.(list_ int_) (List.map hash l)
    | Imply (f1, f2) ->
      h |> CCHash.int_ h_imply |> CCHash.int_ (hash f1) |> CCHash.int_ (hash f2)
    | Equiv (f1, f2) ->
      h |> CCHash.int_ h_equiv |> CCHash.int_ (hash f1) |> CCHash.int_ (hash f2)
    | All (l, _, f) ->
      h |> CCHash.int_ h_all |> CCHash.list_ Id.hash_aux l |> CCHash.int_ (hash f)
    | AllTy (l, _, f) ->
      h |> CCHash.int_ h_allty |> CCHash.list_ Id.hash_aux l |> CCHash.int_ (hash f)
    | Ex (l, _, f) ->
      h |> CCHash.int_ h_ex |> CCHash.list_ Id.hash_aux l |> CCHash.int_ (hash f)
    | ExTy (l, _, f) ->
      h |> CCHash.int_ h_exty |> CCHash.list_ Id.hash_aux l |> CCHash.int_ (hash f)

  and hash f =
    if f.f_hash = -1 then
      f.f_hash <- CCHash.apply hash_aux f;
    f.f_hash

  let discr f = match f.formula with
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

  let rec compare f g =
    let hf = hash f and hg = hash g in
    if hf <> hg then Pervasives.compare hf hg
    else match f.formula, g.formula with
      | True, True | False, False -> 0
      | Equal (u1, v1), Equal(u2, v2) -> Util.lexicograph Term.compare [u1; v1] [u2; v2]
      | Pred t1, Pred t2 -> Term.compare t1 t2
      | Not h1, Not h2 -> compare h1 h2
      | And l1, And l2 -> Util.lexicograph compare l1 l2
      | Or l1, Or l2 -> Util.lexicograph compare l1 l2
      | Imply (h1, i1), Imply (h2, i2) -> Util.lexicograph compare [h1; i1] [h2; i2]
      | Equiv (h1, i1), Equiv (h2, i2) -> Util.lexicograph compare [h1; i1] [h2; i2]
      | All (l1, _, h1), All (l2, _, h2) ->
        begin match Util.lexicograph Id.compare l1 l2 with
          | 0 -> compare h1 h2
          | x -> x
        end
      | AllTy (l1, _, h1), AllTy (l2, _, h2) ->
        begin match Util.lexicograph Id.compare l1 l2 with
          | 0 -> compare h1 h2
          | x -> x
        end
      | Ex (l1, _, h1), Ex (l2, _, h2) ->
        begin match Util.lexicograph Id.compare l1 l2 with
          | 0 -> compare h1 h2
          | x -> x
        end
      | ExTy (l1, _, h1), ExTy (l2, _, h2) ->
        begin match Util.lexicograph Id.compare l1 l2 with
          | 0 -> compare h1 h2
          | x -> x
        end
      | _, _ -> Pervasives.compare (discr f) (discr g)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.formula
  let debug = Debug.formula

  (* Tags *)
  let get_tag f k = Tag.get f.f_tags k
  let tag f k v = { f with f_tags = Tag.add f.f_tags k v }

  (* Free variables *)
  let rec free_vars f = match f.formula with
    | Pred t -> Term.fv t
    | True | False -> Id.null_fv
    | Equal (a, b) -> Id.merge_fv (Term.fv a) (Term.fv b)
    | Not p -> fv p
    | And l | Or l ->
      let l' = List.map fv l in
      List.fold_left Id.merge_fv Id.null_fv l'
    | Imply (p, q) | Equiv (p, q) ->
      Id.merge_fv (fv p) (fv q)
    | AllTy (l, _, p) | ExTy (l, _, p) ->
      Id.remove_fv (fv p) (l, [])
    | All (l, _, p) | Ex (l, _, p) ->
      Id.remove_fv (fv p) ([], l)

  and fv f = match f.f_vars with
    | Some res -> res
    | None ->
      let res = free_vars f in
      f.f_vars <- Some res;
      res

  let to_free_args (tys, ts) = List.map Ty.of_id tys, List.map Term.of_id ts

  (* Constructors *)
  let mk_formula f = {
    formula = f;
    f_hash = -1;
    f_tags = Tag.empty;
    f_vars = None;
  }

  let eq a b =
    if not (Ty.equal a.t_type b.t_type) then
      raise (Type_error_mismatch (a.t_type, b.t_type))
    else if (Ty.equal Ty.prop a.t_type) then
      raise (Type_error_mismatch (Ty.prop, a.t_type))
    else if (Ty.equal Ty.prop b.t_type) then
      raise (Type_error_mismatch (Ty.prop, b.t_type))
    else
    if Term.compare a b < 0 then
      mk_formula (Equal (a, b))
    else
      mk_formula (Equal (b, a))

  let pred t =
    if not (Ty.equal Ty.prop t.t_type) then
      raise (Type_error_mismatch (Ty.prop, t.t_type))
    else
      mk_formula (Pred t)

  let f_true = mk_formula True
  let f_false = mk_formula False

  let neg f = match f.formula with
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

  let imply p q = mk_formula (Imply (p, q))

  let equiv p q = mk_formula (Equiv (p, q))

  let all l f =
    if l = [] then f else
      let l, f = match f.formula with
        | All (l', _, f') -> l @ l', f'
        | _ -> l, f
      in
      let fv = fv (mk_formula (All (l, ([], []), f))) in
      Id.init_term_skolems l fv;
      mk_formula (All (l, to_free_args fv, f))

  let allty l f =
    if l = [] then f else
      let l, f = match f.formula with
        | AllTy (l', _, f') -> l @ l', f'
        | _ -> l, f
      in
      let fv = fv (mk_formula (AllTy (l, ([], []), f))) in
      Id.init_ty_skolems l fv;
      mk_formula (AllTy (l, to_free_args fv, f))

  let ex l f =
    if l = [] then f else
      let l, f = match f.formula with
        | Ex (l', _, f') -> l @ l', f'
        | _ -> l, f
      in
      let fv = fv (mk_formula (Ex (l, ([], []), f))) in
      Id.init_term_skolems l fv;
      mk_formula (Ex (l, to_free_args fv, f))

  let exty l f =
    if l = [] then f else
      let l, f = match f.formula with
        | AllTy (l', _, f') -> l @ l', f'
        | _ -> l, f
      in
      let fv = fv (mk_formula (ExTy (l, ([], []), f))) in
      Id.init_ty_skolems l fv;
      mk_formula (ExTy (l, to_free_args fv, f))

  let rec new_binder_subst ty_map subst acc = function
    | [] -> List.rev acc, subst
    | v :: r ->
      let ty = Ty.subst ty_map v.id_type in
      if not (Ty.equal ty v.id_type) then
        let nv = Id.ty v.id_name ty in
        new_binder_subst ty_map (Subst.Id.bind v (Term.of_id nv) subst) (nv :: acc) r
      else
        new_binder_subst ty_map (Subst.Id.remove v subst) (v :: acc) r

  (* TODO: Check free variables of substitutions for quantifiers ? *)
  let rec formula_subst ty_map t_map f =
    match f.formula with
    | True | False -> f
    | Equal (a, b) ->
      let new_a = Term.subst ty_map t_map a in
      let new_b = Term.subst ty_map t_map b in
      if a == new_a && b == new_b then f
      else eq new_a new_b
    | Pred t ->
      let new_t = Term.subst ty_map t_map t in
      if t == new_t then f
      else pred new_t
    | Not p ->
      let new_p = formula_subst ty_map t_map p in
      if p == new_p then f
      else neg new_p
    | And l ->
      let new_l = List.map (formula_subst ty_map t_map) l in
      if List.for_all2 (==) l new_l then f
      else f_and new_l
    | Or l ->
      let new_l = List.map (formula_subst ty_map t_map) l in
      if List.for_all2 (==) l new_l then f
      else f_or new_l
    | Imply (p, q) ->
      let new_p = formula_subst ty_map t_map p in
      let new_q = formula_subst ty_map t_map q in
      if p == new_p && q == new_q then f
      else imply new_p new_q
    | Equiv (p, q) ->
      let new_p = formula_subst ty_map t_map p in
      let new_q = formula_subst ty_map t_map q in
      if p == new_p && q == new_q then f
      else equiv new_p new_q
    | All (l, (ty, t), p) ->
      let l', t_map = new_binder_subst ty_map t_map [] l in
      let tys = List.map (Ty.subst ty_map) ty in
      let ts = List.map (Term.subst ty_map t_map) t in
      mk_formula (All (l', (tys, ts), (formula_subst ty_map t_map p)))
    | Ex (l, (ty, t), p) ->
      let l', t_map = new_binder_subst ty_map t_map [] l in
      let tys = List.map (Ty.subst ty_map) ty in
      let ts = List.map (Term.subst ty_map t_map) t in
      mk_formula (Ex (l', (tys, ts), (formula_subst ty_map t_map p)))
    | AllTy (l, (ty, t), p) ->
      assert (t = []);
      let tys = List.map (Ty.subst ty_map) ty in
      mk_formula (AllTy (l, (tys, t), (formula_subst ty_map t_map p)))
    | ExTy (l, (ty, t), p) ->
      assert (t = []);
      let tys = List.map (Ty.subst ty_map) ty in
      mk_formula (ExTy (l, (tys, t), (formula_subst ty_map t_map p)))

  let subst ty_map t_map f =
    Subst.iter (fun _ ty -> match ty.ty with TyVar _ -> assert false | _ -> ()) ty_map;
    Subst.iter (fun _ t -> match t.term with Var _ -> assert false | _ -> ()) t_map;
    if Subst.is_empty ty_map && Subst.is_empty t_map then f
    else formula_subst ty_map t_map f

  let partial_inst ty_map t_map f = match f.formula with
    | All (l, args, p) ->
      let l' = List.filter (fun v -> not (Subst.Id.mem v t_map)) l in
      let q = formula_subst ty_map t_map p in
      if l' = [] then q else mk_formula (All (l', args, q))
    | AllTy (l, args, p) ->
      let l' = List.filter (fun v -> not (Subst.Id.mem v ty_map)) l in
      let q = formula_subst ty_map t_map p in
      if l' = [] then q else mk_formula (AllTy (l', args, q))
    | Not { formula = Ex (l, args, p) } ->
      let l' = List.filter (fun v -> not (Subst.Id.mem v t_map)) l in
      let q = formula_subst ty_map t_map p in
      neg (if l' = [] then q else mk_formula (Ex (l', args, q)))
    | Not { formula = ExTy (l, args, p) } ->
      let l' = List.filter (fun v -> not (Subst.Id.mem v ty_map)) l in
      let q = formula_subst ty_map t_map p in
      neg (if l' = [] then q else mk_formula (ExTy (l', args, q)))
    | _ -> f
end

