(*
   Base modules that defines the terms used in the prover.
*)

(*
let section = Section.make "expr"
*)

(* Type definitions *)
(* ************************************************************************ *)

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
  mutable id_tags : tag_map;
}

(* Metavariables, basically, wrapped variables *)
type 'ty meta = {
  meta_id : 'ty id;
  meta_index : 'ty meta_index;
}

(* Type for first order types *)
type ttype = Type

(* The type of functions *)
type ('ttype, 'ty) function_descr = {
  fun_vars : 'ttype id list; (* prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

(* Types *)
type ty_descr =
  | TyVar of ttype id (** Bound variables *)
  | TyMeta of ttype meta
  | TyApp of (unit, ttype) function_descr id * ty list

and ty = {
  ty : ty_descr;
  ty_status : status;
  mutable ty_tags : tag_map;
  mutable ty_hash : hash; (** lazy hash *)
}

(* Terms & formulas *)
type term_descr =
  | Var of ty id
  | Meta of ty meta
  | App of (ttype, ty) function_descr id * ty list * term list

and term = {
  term    : term_descr;
  t_type  : ty;
  t_status : status;
  mutable t_tags : tag_map;
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
  formula : formula_descr;
  mutable f_tags : tag_map;
  mutable f_hash  : hash; (* lazy hash *)
  mutable f_vars : (ttype id list * ty id list) option;
}

(* Original order or expresisons *)
(* ************************************************************************ *)

(* This type and tag will represent the original ordering of arguments for
   constructions that changes it, such as:
   - equality (which orders itw two arguments using the term ordering)
   - and/or (which flattens the list and lose the tree structure)
   - others ? *)
type t_order =
  | Same
  | Inverse

type 'a order =
  | F of 'a
  | L of 'a order list

type f_order = formula order

let t_order : t_order Tag.t = Tag.create ()
let f_order : f_order Tag.t = Tag.create ()

module Order = struct

  let rec map f = function
    | F x -> F (f x)
    | L l -> L (List.map (map f) l)

  let rec for_all2 p o o' =
    match o, o' with
    | F x, F y -> p x y
    | L l, L l' -> List.for_all2 (for_all2 p) l l'
    | _ -> false

  let rec build mk = function
    | F x -> x
    | L l -> mk (List.map (build mk) l)

end

(* Exceptions *)
(* ************************************************************************ *)

exception Type_mismatch of term * ty * ty
exception Bad_arity of (ttype, ty) function_descr id * ty list * term list
exception Bad_ty_arity of (unit, ttype) function_descr id * ty list

exception Cannot_assign of term
exception Cannot_interpret of term

(* Status settings *)
(* ************************************************************************ *)

module Status = struct
  let goal = 1
  let hypothesis = 0
end

(* Printing functions *)
(* ************************************************************************ *)

module Print = struct

  let pos : Pretty.pos tag = Tag.create ()
  let name : Pretty.name tag = Tag.create ()

  let get_name v =
    match Tag.get v.id_tags name with
    | None -> v.id_name
    | Some s -> s

  let id fmt v = Format.fprintf fmt "%s" (get_name v)
  let meta fmt m = Format.fprintf fmt "m%d_%a" m.meta_index id m.meta_id
  let ttype fmt = function Type -> Format.fprintf fmt "Type"

  let rec ty fmt t = match t.ty with
    | TyVar v -> id fmt v
    | TyMeta m -> meta fmt m
    | TyApp (f, []) -> id fmt f
    | TyApp (f, l) ->
      begin match Tag.get f.id_tags pos with
        | None ->
          Format.fprintf fmt "@[<hov 2>%a(%a)@]"
            id f CCFormat.(list ~sep:(return ",@ ") ty) l
        | Some Pretty.Prefix ->
          assert (List.length l = 1);
          Format.fprintf fmt "@[<hov 2>%a %a@]"
            id f CCFormat.(list ~sep:(return "") ty) l
        | Some Pretty.Infix ->
          assert (List.length l > 1);
          let sep fmt () = Format.fprintf fmt "%a@ " id f in
          Format.fprintf fmt "@[<hov 2>%a@]" (CCFormat.list ~sep ty) l
      end

  let params fmt = function
    | [] -> ()
    | l -> Format.fprintf fmt "∀ @[<hov>%a@].@ "
             CCFormat.(list ~sep:(return ",@ ") id) l

  let signature print fmt f =
    match f.fun_args with
    | [] -> Format.fprintf fmt "@[<hov 2>%a%a@]" params f.fun_vars print f.fun_ret
    | l -> Format.fprintf fmt "@[<hov 2>%a%a ->@ %a@]" params f.fun_vars
             CCFormat.(list ~sep:(return " ->@ ") print) l print f.fun_ret

  let fun_ty = signature ty
  let fun_ttype = signature ttype

  let id_pretty fmt v =
    match Tag.get v.id_tags pos with
    | None -> ()
    | Some Pretty.Infix -> Format.fprintf fmt "(%a)" id v
    | Some Pretty.Prefix -> Format.fprintf fmt "[%a]" id v

  let id_type print fmt v =
    Format.fprintf fmt "@[<hov 2>%a%a :@ %a@]" id v id_pretty v print v.id_type

  let id_ty = id_type ty
  let id_ttype = id_type ttype
  let const_ty = id_type fun_ty
  let const_ttype = id_type fun_ttype

  let rec term fmt t = match t.term with
    | Var v -> id fmt v
    | Meta m -> meta fmt m
    | App (f, [], []) -> id fmt f
    | App (f, tys, args) ->
      begin match Tag.get f.id_tags pos with
        | None ->
          begin match tys, args with
            | _, [] ->
              Format.fprintf fmt "%a(@[<hov>%a@])"
                id f CCFormat.(list ~sep:(return ",@ ") ty) tys
            | [], _ ->
              Format.fprintf fmt "%a(@[<hov>%a@])"
                id f CCFormat.(list ~sep:(return ",@ ") term) args
            | _ ->
              Format.fprintf fmt "%a(@[<hov>%a%a%a@])" id f
                CCFormat.(list ~sep:(return ",@ ") ty) tys
                CCFormat.(return ";@ ") ()
                CCFormat.(list ~sep:(return ",@ ") term) args
          end
        | Some Pretty.Prefix ->
          begin match args with
            | [] -> id fmt f
            | _ ->
              Format.fprintf fmt "@[<hov>%a(%a)@]"
                id f CCFormat.(list ~sep:(return ",@ ") term) args
          end
        | Some Pretty.Infix ->
          assert (List.length args >= 2);
          let sep fmt () = Format.fprintf fmt " %a@ " id f in
          Format.fprintf fmt "(@[<hov>%a@])" CCFormat.(list ~sep term) args
      end

  let rec formula_aux fmt f =
    let aux fmt f = match f.formula with
      | Equal _ | Pred _ | True | False -> formula_aux fmt f
      | _ -> Format.fprintf fmt "@[<hov 2>( %a )@]" formula_aux f
    in
    match f.formula with
    | Pred t -> Format.fprintf fmt "%a" term t
    | Equal (a, b) -> Format.fprintf fmt "@[<hv>%a =@ %a@]" term a term b

    | True  -> Format.fprintf fmt "⊤"
    | False -> Format.fprintf fmt "⊥"
    | Not f -> Format.fprintf fmt "@[<hov 2>¬ %a@]" aux f
    | And l -> Format.fprintf fmt "@[<hv>%a@]" CCFormat.(list ~sep:(return " ∧@ ") aux) l
    | Or l  -> Format.fprintf fmt "@[<hv>%a@]" CCFormat.(list ~sep:(return " ∨@ ") aux) l

    | Imply (p, q)    -> Format.fprintf fmt "@[<hv>%a ⇒@ %a@]" aux p aux q
    | Equiv (p, q)    -> Format.fprintf fmt "@[<hv>%a ⇔@ %a@]" aux p aux q

    | All (l, _, f)   -> Format.fprintf fmt "@[<hv 2>∀ @[<hov>%a@].@ %a@]"
                           CCFormat.(list ~sep:(return ",@ ") id_ty) l formula_aux f
    | AllTy (l, _, f) -> Format.fprintf fmt "@[<hv 2>∀ @[<hov>%a@].@ %a@]"
                           CCFormat.(list ~sep:(return ",@ ") id_ttype) l formula_aux f
    | Ex (l, _, f)    -> Format.fprintf fmt "@[<hv 2>∃ @[<hov>%a@].@ %a@]"
                           CCFormat.(list ~sep:(return ",@ ") id_ty) l formula_aux f
    | ExTy (l, _, f)  -> Format.fprintf fmt "@[<hv 2>∃ @[<hov>%a@].@ %a@]"
                           CCFormat.(list ~sep:(return ",@ ") id_ttype) l formula_aux f

  let formula fmt f = Format.fprintf fmt "⟦@[<hov>%a@]⟧" formula_aux f

end

(* Substitutions *)
(* ************************************************************************ *)

module Subst = struct
  module Mi = CCMap.Make(struct
      type t = int * int
      let compare (a, b) (c, d) = match compare a c with 0 -> compare b d | x -> x
    end)

  type ('a, 'b) t = ('a * 'b) Mi.t

  (* Usual functions *)
  let empty = Mi.empty

  let is_empty = Mi.is_empty

  let wrap key = function
    | None -> None
    | Some x -> Some (key, x)

  let merge f = Mi.merge (fun _ opt1 opt2 ->
      match opt1, opt2 with
      | None, None -> assert false
      | Some (key, value), None ->
        wrap key @@ f key (Some value) None
      | None, Some (key, value) ->
        wrap key @@ f key None (Some value)
      | Some (key, value1), Some (_key, value2) ->
        wrap key @@ f key (Some value1) (Some value2)
    )

  let iter f = Mi.iter (fun _ (key, value) -> f key value)

  let map f = Mi.map (fun (key, value) -> (key, f value))

  let fold f = Mi.fold (fun _ (key, value) acc -> f key value acc)

  let bindings s = Mi.fold (fun _ (key, value) acc -> (key, value) :: acc) s []

  let filter p = Mi.filter (fun _ (key, value) -> p key value)

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

  let print print_key print_value fmt map =
    let aux fmt (key, value) =
      Format.fprintf fmt "@[<hov>%a ↦@ %a@]" print_key key print_value value
    in
    Format.fprintf fmt "@[<hov>%a@]"
      CCFormat.(seq ~sep:(return ";@ ") aux) (Mi.values map)

  (* Specific substitutions signature *)
  module type S = sig
    type 'a key
    val get : 'a key -> ('a key, 'b) t -> 'b
    val mem : 'a key -> ('a key, 'b) t -> bool
    val bind : ('a key, 'b) t -> 'a key -> 'b -> ('a key, 'b) t
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
  end

  (* Variable substitutions *)
  module Id = struct
    type 'a key = 'a id
    let tok v = (v.index, 0)
    let get v s = snd (Mi.find (tok v) s)
    let mem v s = Mi.mem (tok v) s
    let bind s v t = Mi.add (tok v) (v, t) s
    let remove v s = Mi.remove (tok v) s
  end

  (* Meta substitutions *)
  module Meta = struct
    type 'a key = 'a meta
    let tok m = (m.meta_id.index, m.meta_index)
    let get m s = snd (Mi.find (tok m) s)
    let mem m s = Mi.mem (tok m) s
    let bind s m t = Mi.add (tok m) (m, t) s
    let remove m s = Mi.remove (tok m) s
  end


end

(* Variables *)
(* ************************************************************************ *)

module Id = struct
  type 'a t = 'a id

  (* Hash & comparisons *)
  let hash v = CCHash.int v.index

  let compare: 'a. 'a id -> 'a id -> int =
    fun v1 v2 -> compare v1.index v2.index

  let equal v1 v2 = compare v1 v2 = 0

  (* Printing functions *)
  let print = Print.id

  (* Some convenience modules for functor instanciation *)
  module Ty = struct
    type t = ty id
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end
  module Ttype = struct
    type t = ttype id
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end
  module Const = struct
    type t = (ttype, ty) function_descr id
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end
  module TyCstr = struct
    type t = (unit, ttype) function_descr id
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end

  (* Internal state *)
  let eval_vec = CCVector.create ()
  let assign_vec = CCVector.create ()
  let ty_skolems = Hashtbl.create 17
  let term_skolems = Hashtbl.create 1007

  (* Constructors *)
  let mk_new ?(builtin=Base) ?(tags=Tag.empty) id_name id_type =
    assert (CCVector.length eval_vec = CCVector.length assign_vec);
    assert (id_name <> "");
    let index = CCVector.length eval_vec in
    let id_tags = tags in
    CCVector.push eval_vec None;
    CCVector.push assign_vec None;
    { index; id_name; id_type; id_tags; builtin }

  let fresh v =
    mk_new ~builtin:v.builtin ~tags:v.id_tags v.id_name v.id_type

  let ttype ?builtin ?tags name = mk_new ?builtin ?tags name Type
  let ty ?builtin ?tags name ty = mk_new ?builtin ?tags name ty

  let const ?builtin ?tags name fun_vars fun_args fun_ret =
    mk_new ?builtin ?tags name { fun_vars; fun_args; fun_ret; }

  let ty_fun ?builtin ?tags name n =
    const ?builtin ?tags name [] (CCList.replicate n Type) Type
  let term_fun = const

  (* Tags *)
  let get_tag id k = Tag.get id.id_tags k

  let tag id k v =
    id.id_tags <- Tag.add id.id_tags k v

  let cached f =
    let t = Tag.create () in
    (function id ->
     match get_tag id t with
     | Some res -> res
     | None ->
       let res = f id in
       tag id t res;
       res
    )

  (* Builtin Types *)
  let prop = ty_fun "$o" 0
  let base = ty_fun "$i" 0

  (* Free variables *)
  let null_fv = [], []

  let merge_fv (ty1, t1) (ty2, t2) =
    CCList.sorted_merge_uniq ~cmp:compare ty1 ty2,
    CCList.sorted_merge_uniq ~cmp:compare t1 t2

  let remove_fv (ty1, t1) (ty2, t2) =
    List.filter (fun v -> not (CCList.mem ~eq:equal v ty2)) ty1,
    List.filter (fun v -> not (CCList.mem ~eq:equal v t2)) t1

  let rec free_ty acc ty = match ty.ty with
    | TyVar v -> merge_fv acc ([v], [])
    | TyMeta _ -> acc
    | TyApp (_, args) -> List.fold_left free_ty acc args

  let rec free_term acc t = match t.term with
    | Var v -> merge_fv acc ([], [v])
    | Meta _ -> acc
    | App (_, tys, args) ->
      let acc' = List.fold_left free_ty acc tys in
      List.fold_left free_term acc' args

  (* Variable occurs in a term *)
  let rec occurs_in_term var t = match t.term with
    | Var v -> equal var v
    | Meta _ -> false
    | App (f, _, args) ->
      List.exists (occurs_in_term var) args

  (* Evaluation *)
  let is_interpreted f =
    CCVector.get eval_vec f.index <> None

  let interpreter v =
    match CCVector.get eval_vec v.index with
    | None -> (fun _ -> raise Exit)
    | Some (_, f) -> f

  let set_eval v (prio: int) (f: term -> unit) =
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

  let set_assign v (prio: int) f =
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
    let res = ty_fun (Format.sprintf "sk_%s%d" v.id_name v.index) n in
    Hashtbl.add ty_skolems v.index res

  let init_term_skolem v tys args ret =
    let res = term_fun (Format.sprintf "sk_%s%d" v.id_name v.index) tys args ret in
    Hashtbl.add term_skolems v.index res

  let init_ty_skolems l (ty_vars, t_vars) =
    assert (t_vars = []); (* Else we would have dependent types *)
    let n = List.length ty_vars in
    List.iter (fun v -> init_ty_skolem v n) l

  let init_term_skolems l (ty_vars, t_vars) =
    let args_types = List.map (fun v -> v.id_type) t_vars in
    List.iter (fun v -> init_term_skolem v ty_vars args_types v.id_type) l

  let copy_term_skolem v v' =
    let old = term_skolem v in
    Hashtbl.add term_skolems v'.index old

end

(* Meta-variables *)
(* ************************************************************************ *)

module Meta = struct
  type 'a t = 'a meta

  (* Hash & Comparisons *)
  let hash m = CCHash.int m.meta_id.index

  let compare m1 m2 =
    match compare m1.meta_index m2.meta_index with
    | 0 -> Id.compare m1.meta_id m2.meta_id
    | x -> x

  let equal m1 m2 = compare m1 m2 = 0

  (* Printing functions *)
  let print = Print.meta

  (* Some convenience modules for functor instanciation *)
  module Ty = struct
    type t = ty meta
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end
  module Ttype = struct
    type t = ttype meta
    let hash = hash
    let equal = equal
    let compare = compare
    let print = print
  end

  (* Free meta-variables *)
  let null_fm = [], []

  let merge_fm (ty1, t1) (ty2, t2) =
    CCList.sorted_merge_uniq ~cmp:compare ty1 ty2,
    CCList.sorted_merge_uniq ~cmp:compare t1 t2

  let remove_fm (ty1, t1) (ty2, t2) =
    List.filter (fun v -> not (CCList.mem ~eq:equal v ty2)) ty1,
    List.filter (fun v -> not (CCList.mem ~eq:equal v t2)) t1

  let rec free_ty acc ty = match ty.ty with
    | TyVar _ -> acc
    | TyMeta m -> merge_fm acc ([m], [])
    | TyApp (_, args) -> List.fold_left free_ty acc args

  let rec free_term acc t = match t.term with
    | Var _ -> acc
    | Meta m -> merge_fm acc ([], [m])
    | App (_, tys, args) ->
      let acc' = List.fold_left free_ty acc tys in
      List.fold_left free_term acc' args

  let rec free_formula acc t = match t.formula with
    | Pred p -> free_term acc p
    | Equal (a, b) -> free_term (free_term acc a) b
    | True | False -> acc
    | Not f -> free_formula acc f
    | And l
    | Or l -> List.fold_left free_formula acc l
    | Imply (p, q)
    | Equiv (p, q) ->
      free_formula (free_formula acc p) q
    | All (_, _, f)
    | AllTy (_, _, f)
    | Ex (_, _, f)
    | ExTy (_, _, f) ->
      free_formula acc f

  (* Metas refer to an index which stores the defining formula for the variable *)
  type meta_def =
    | Term of formula * ty meta list
    | Ty of formula * ttype meta list

  let meta_index = CCVector.create ()

  (* Metas *)
  let mk_meta v i = {
    meta_id = v;
    meta_index = i;
  }

  let ty_def i =
    match CCVector.get meta_index i with
    | Term (f, _) -> f
    | Ty _ -> invalid_arg "ty_def"

  let ttype_def i =
    match CCVector.get meta_index i with
    | Ty (f, _) -> f
    | Term _ -> invalid_arg "ttype_def"

  let of_ttype_index i =
    match CCVector.get meta_index i with
    | Ty (_, l) -> l
    | Term _ -> invalid_arg "of_ttype_index"

  let of_ty_index i =
    match CCVector.get meta_index i with
    | Term (_, l) -> l
    | Ty _ -> invalid_arg "of_ty_index"

  let mk_metas l f =
    let i = CCVector.size meta_index in
    let metas = List.map (fun v -> mk_meta v i) l in
    CCVector.push meta_index (Term (f, metas));
    metas

  let mk_ty_metas l f =
    let i = CCVector.size meta_index in
    let metas = List.map (fun v -> mk_meta v i) l in
    CCVector.push meta_index (Ty (f, metas));
    metas

  let of_all_ty f = match f.formula with
    | Not { formula = ExTy(l, _, _) } | AllTy (l, _, _) -> mk_ty_metas l f
    | _ -> invalid_arg "new_ty_metas"

  let of_all f = match f.formula with
    | Not { formula = Ex(l, _, _) } | All (l, _, _) -> mk_metas l f
    | _ -> invalid_arg "new_term_metas"

  (* Meta-variable occurs in a term *)
  let rec occurs_in_term meta t = match t.term with
    | Var v -> false
    | Meta m -> equal meta m
    | App (f, _, args) ->
      List.exists (occurs_in_term meta) args

end

(* Types *)
(* ************************************************************************ *)

module Ty = struct

  type t = ty
  type var_subst = (ttype id, ty) Subst.t
  type meta_subst = (ttype meta, ty) Subst.t

  (* Hash & Comparisons *)
  let rec hash_aux t = match t.ty with
    | TyVar v -> Id.hash v
    | TyMeta m -> Meta.hash m
    | TyApp (f, args) ->
      CCHash.combine2 (Id.hash f) (CCHash.list hash args)

  and hash t =
    if t.ty_hash = -1 then t.ty_hash <- hash_aux t;
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
        CCOrd.Infix.(Id.compare f1 f2
                     <?> (CCOrd.list compare, args1, args2))
      | _, _ -> Pervasives.compare (discr u) (discr v)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.ty

  (* Constructors *)
  let mk_ty ?(status=Status.hypothesis) ty =
    { ty; ty_status = status; ty_hash = -1; ty_tags = Tag.empty; }

  let of_id ?status v = mk_ty ?status (TyVar v)

  let of_meta ?status m = mk_ty ?status (TyMeta m)

  let apply ?status f args =
    assert (f.id_type.fun_vars = []);
    if List.length args <> List.length f.id_type.fun_args then
      raise (Bad_ty_arity (f, args))
    else
      mk_ty ?status (TyApp (f, args))

  (* Tags *)
  let get_tag ty k = Tag.get ty.ty_tags k
  let tag ty k v = ty.ty_tags <- Tag.add ty.ty_tags k v
  let cached f =
    let t = Tag.create () in
    (function ty ->
     match get_tag ty t with
     | Some res -> res
     | None ->
       let res = f ty in
       tag ty t res;
       res
    )

  (* Builtin types *)
  let prop = apply Id.prop []
  let base = apply Id.base []

  (* Substitutions *)
  let rec subst_aux ~fix var_map meta_map t = match t.ty with
    | TyVar v ->
      begin match Subst.Id.get v var_map with
        | exception Not_found -> t
        | ty -> if fix then subst_aux ~fix var_map meta_map ty else ty
      end
    | TyMeta m ->
      begin match Subst.Meta.get m meta_map with
        | exception Not_found -> t
        | ty -> if fix then subst_aux ~fix var_map meta_map ty else ty
      end
    | TyApp (f, args) ->
      let new_args = List.map (subst_aux ~fix var_map meta_map) args in
      if List.for_all2 (==) args new_args then t
      else apply ~status:t.ty_status f new_args

  let subst ?(fix=true) var_map meta_map t =
    if Subst.is_empty var_map && Subst.is_empty meta_map then t
    else subst_aux ~fix var_map meta_map t

  (* Typechecking *)
  let instantiate f tys args =
    if List.length f.id_type.fun_vars <> List.length tys ||
       List.length f.id_type.fun_args <> List.length args then
      raise (Bad_arity (f, tys, args))
    else
      let map = List.fold_left2 Subst.Id.bind Subst.empty f.id_type.fun_vars tys in
      let fun_args = List.map (subst map Subst.empty) f.id_type.fun_args in
      List.iter2 (fun t ty ->
          if not (equal t.t_type ty) then raise (Type_mismatch (t, t.t_type, ty)))
        args fun_args;
      subst map Subst.empty f.id_type.fun_ret

  (* Free variables *)
  let fv = Id.free_ty Id.null_fv
  let fm = Meta.free_ty Meta.null_fm

end

(* Terms *)
(* ************************************************************************ *)

module Term = struct

  type t = term
  type var_subst = (ty id, term) Subst.t
  type meta_subst = (ty meta, term) Subst.t

  (* Hash & Comparisons *)
  let rec hash_aux t = match t.term with
    | Var v -> Id.hash v
    | Meta m -> Meta.hash m
    | App (f, tys, args) ->
      CCHash.combine3
        (Id.hash f)
        (CCHash.list Ty.hash tys)
        (CCHash.list hash args)

  and hash t =
    if t.t_hash = -1 then t.t_hash <- hash_aux t;
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
        CCOrd.Infix.(Id.compare f1 f2
                     <?> (CCOrd.list Ty.compare, tys1, tys2)
                     <?> (CCOrd.list compare, args1, args2))
      | _, _ -> Pervasives.compare (discr u) (discr v)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.term

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
  let tag t k v = t.t_tags <- Tag.add t.t_tags k v
  let cached f =
    let t = Tag.create () in
    (function term ->
     match get_tag term t with
     | Some res -> res
     | None ->
       let res = f term in
       tag term t res;
       res
    )

  (* Substitutions *)
  let rec subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map t =
    match t.term with
    | Var v ->
      begin match Subst.Id.get v t_var_map with
        | exception Not_found -> t
        | term ->
          if fix
          then subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map term
          else term
      end
    | Meta m ->
      begin match Subst.Meta.get m t_meta_map with
        | exception Not_found -> t
        | term ->
          if fix
          then subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map term
          else term
      end
    | App (f, tys, args) ->
      let new_tys = List.map (Ty.subst ~fix ty_var_map ty_meta_map) tys in
      let new_args = List.map (subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map) args in
      if List.for_all2 (==) new_tys tys && List.for_all2 (==) new_args args then t
      else apply ~status:t.t_status f new_tys new_args

  let subst ?(fix=true) ty_var_map ty_meta_map t_var_map t_meta_map t =
    if Subst.is_empty ty_var_map && Subst.is_empty ty_meta_map &&
       Subst.is_empty t_var_map && Subst.is_empty t_meta_map then
      t
    else
      subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map t

  let rec replace (t, t') t'' = match t''.term with
    | _ when equal t t'' -> t'
    | App (f, ty_args, t_args) ->
      apply ~status:t''.t_status f ty_args (List.map (replace (t, t')) t_args)
    | _ -> t''

  (* Free variables *)
  let fv = Id.free_term Id.null_fv
  let fm = Meta.free_term Meta.null_fm

  (* Evaluation & Assignment *)
  let eval ?(strict=false) t =
    try
      match t.term with
      | Var v -> (Id.interpreter v) t
      | Meta m -> (Id.interpreter m.meta_id) t
      | App (f, _, _) -> (Id.interpreter f) t
    with Exit ->
      if strict then raise (Cannot_interpret t)

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
  type var_subst = (ty id, formula) Subst.t
  type meta_subst = (ty meta, formula) Subst.t

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

  let rec hash_aux f = match f.formula with
    | Pred t ->
      CCHash.combine2 h_pred (Term.hash t)
    | Equal (t1, t2) ->
      CCHash.combine3 h_eq (Term.hash t1) (Term.hash t2)
    | True ->
      CCHash.int h_true
    | False ->
      CCHash.int h_false
    | Not f ->
      CCHash.combine2 h_not (hash f)
    | And l ->
      CCHash.combine2 h_and (CCHash.list hash l)
    | Or l ->
      CCHash.combine2 h_or (CCHash.list hash l)
    | Imply (f1, f2) ->
      CCHash.combine3 h_imply (hash f1) (hash f2)
    | Equiv (f1, f2) ->
      CCHash.combine3 h_equiv (hash f1) (hash f2)
    | All (l, _, f) ->
      CCHash.combine3 h_all (CCHash.list Id.hash l) (hash f)
    | AllTy (l, _, f) ->
      CCHash.combine3 h_allty (CCHash.list Id.hash l) (hash f)
    | Ex (l, _, f) ->
      CCHash.combine3 h_ex (CCHash.list Id.hash l) (hash f)
    | ExTy (l, _, f) ->
      CCHash.combine3 h_exty (CCHash.list Id.hash l) (hash f)

  and hash f =
    if f.f_hash = -1 then f.f_hash <- hash_aux f;
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
      | Equal (u1, v1), Equal(u2, v2) ->
        CCOrd.pair Term.compare Term.compare (u1, v1) (u2, v2)
      | Pred t1, Pred t2  -> Term.compare t1 t2
      | Not h1, Not h2    -> compare h1 h2
      | And l1, And l2    -> CCOrd.list compare l1 l2
      | Or l1, Or l2      -> CCOrd.list compare l1 l2
      | Imply (h1, i1), Imply (h2, i2)
      | Equiv (h1, i1), Equiv (h2, i2) ->
        CCOrd.pair compare compare (h1, i1) (h2, i2)
      | Ex (l1, _, h1), Ex (l2, _, h2)
      | All (l1, _, h1), All (l2, _, h2) ->
        CCOrd.Infix.(CCOrd.list Id.compare l1 l2
                     <?> (compare, h1, h2))
      | ExTy (l1, _, h1), ExTy (l2, _, h2)
      | AllTy (l1, _, h1), AllTy (l2, _, h2) ->
        CCOrd.Infix.(CCOrd.list Id.compare l1 l2
                     <?> (compare, h1, h2))
      | _, _ -> Pervasives.compare (discr f) (discr g)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let print = Print.formula

  (* Tags *)
  let get_tag f k = Tag.get f.f_tags k
  let tag f k v = f.f_tags <- Tag.add f.f_tags k v

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
      let v = List.fold_left (fun acc x ->
          Id.merge_fv acc (Ty.fv x.id_type)) (fv p) l in
      Id.remove_fv v ([], l)

  and fv f = match f.f_vars with
    | Some res -> res
    | None ->
      let res = free_vars f in
      f.f_vars <- Some res;
      res

  let fm f = Meta.free_formula ([], []) f

  let to_free_args (tys, ts) = List.map Ty.of_id tys, List.map Term.of_id ts

  (* Constructors *)
  let mk_formula f = {
    formula = f;
    f_hash = -1;
    f_tags = Tag.empty;
    f_vars = None;
  }

  let pred t =
    if not (Ty.equal Ty.prop t.t_type) then
      raise (Type_mismatch (t, t.t_type, Ty.prop))
    else
      mk_formula (Pred t)

  let f_true = mk_formula True
  let f_false = mk_formula False

  let neg f = match f.formula with
    | True -> f_false
    | False -> f_true
    | Not f' -> f'
    | _ -> mk_formula (Not f)

  let check s = function
    | [_] -> Util.warn "Trying to make a %s with only one element" s;
    | _ -> ()

  let f_and l =
    check "conjunction" l;
    let rec aux (o, acc) = function
      | [] -> o, acc
      | ({ formula = And l' } as f) :: r ->
        let t = CCOpt.get_exn @@ get_tag f f_order in
        aux (t :: o, List.rev_append l' acc) r
      | a :: r ->
        aux (F a :: o, a :: acc) r
    in
    match aux ([], []) l with
    | _, [] -> f_false
    | o, l' ->
      let res = mk_formula (And (List.rev l')) in
      let () = tag res f_order (L (List.rev o)) in
      res

  let f_or l =
    check "disjunction" l;
    let rec aux (o, acc) = function
      | [] -> o, acc
      | ({ formula = Or l' } as f) :: r ->
        let t = CCOpt.get_exn @@ get_tag f f_order in
        aux (t :: o, List.rev_append l' acc) r
      | a :: r ->
        aux (F a :: o, a :: acc) r
    in
    match aux ([], []) l with
    | _, [] -> f_true
    | o, l' ->
      let res = mk_formula (Or (List.rev l')) in
      let () = tag res f_order (L (List.rev o)) in
      res

  let imply p q = mk_formula (Imply (p, q))

  let equiv p q = mk_formula (Equiv (p, q))

  let eq a b =
    if not (Ty.equal a.t_type b.t_type) then
      raise (Type_mismatch (b, b.t_type, a.t_type))
    else if (Ty.equal Ty.prop a.t_type) then
      equiv (pred a) (pred b) (* no need to order propositions *)
    else begin
      let order, res =
        if Term.compare a b < 0 then
          Same, mk_formula (Equal (a, b))
        else
          Inverse, mk_formula (Equal (b, a))
      in
      let () = tag res t_order order in
      res
    end


  let rec new_binder_subst ty_var_map ty_meta_map subst acc = function
    | [] -> List.rev acc, subst
    | v :: r ->
      let ty = Ty.subst ty_var_map ty_meta_map v.id_type in
      if not (Ty.equal ty v.id_type) then
        let nv = Id.ty v.id_name ty in
        new_binder_subst ty_var_map ty_meta_map
          (Subst.Id.bind subst v (Term.of_id nv)) (nv :: acc) r
      else
        new_binder_subst ty_var_map ty_meta_map
          (Subst.Id.remove v subst) (v :: acc) r

  (* TODO: Check free variables of substitutions for quantifiers ? *)
  let rec subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap f =
    match f.formula with
    | True | False -> f
    | Equal (a, b) ->
      let a, b =
        match get_tag f t_order with
        | None -> assert false
        | Some Same -> a, b
        | Some Inverse -> b, a
      in
      let new_a = Term.subst ~fix ty_vmap ty_mmap t_vmap t_mmap a in
      let new_b = Term.subst ~fix ty_vmap ty_mmap t_vmap t_mmap b in
      if a == new_a && b == new_b then f
      else eq new_a new_b
    | Pred { term = Var v; } when Subst.Id.mem v f_vmap ->
      subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap (Subst.Id.get v f_vmap)
    | Pred { term = Meta m; } when Subst.Meta.mem m f_mmap ->
      subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap (Subst.Meta.get m f_mmap)
    | Pred t ->
      let new_t = Term.subst ~fix ty_vmap ty_mmap t_vmap t_mmap t in
      if t == new_t then f else pred new_t
    | Not p ->
      let new_p = subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap p in
      if p == new_p then f
      else neg new_p
    | And _ ->
      let o = CCOpt.get_exn @@ get_tag f f_order in
      let o'= Order.map (subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap) o in
      if Order.for_all2 (==) o o' then f
      else Order.build f_and o'
    | Or l ->
      let o = CCOpt.get_exn @@ get_tag f f_order in
      let o'= Order.map (subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap) o in
      if Order.for_all2 (==) o o' then f
      else Order.build f_or o'
    | Imply (p, q) ->
      let new_p = subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap p in
      let new_q = subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap q in
      if p == new_p && q == new_q then f
      else imply new_p new_q
    | Equiv (p, q) ->
      let new_p = subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap p in
      let new_q = subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap q in
      if p == new_p && q == new_q then f
      else equiv new_p new_q
    | All (l, (ty, t), p) ->
      let l', t_map = new_binder_subst ty_vmap ty_mmap t_vmap [] l in
      List.iter2 Id.copy_term_skolem l l';
      let tys = List.map (Ty.subst ~fix ty_vmap ty_mmap) ty in
      let ts = List.map (Term.subst ~fix ty_vmap ty_mmap t_map t_mmap) t in
      mk_formula (All (l', (tys, ts), (subst_aux ~fix ty_vmap ty_mmap t_map t_mmap f_vmap f_mmap p)))
    | Ex (l, (ty, t), p) ->
      let l', t_map = new_binder_subst ty_vmap ty_mmap t_vmap [] l in
      List.iter2 Id.copy_term_skolem l l';
      let tys = List.map (Ty.subst ~fix ty_vmap ty_mmap) ty in
      let ts = List.map (Term.subst ~fix ty_vmap ty_mmap t_map t_mmap) t in
      mk_formula (Ex (l', (tys, ts), (subst_aux ~fix ty_vmap ty_mmap t_map t_mmap f_vmap f_mmap p)))
    | AllTy (l, (ty, t), p) ->
      assert (t = []);
      let tys = List.map (Ty.subst ~fix ty_vmap ty_mmap) ty in
      mk_formula (AllTy (l, (tys, t), (subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap p)))
    | ExTy (l, (ty, t), p) ->
      assert (t = []);
      let tys = List.map (Ty.subst ~fix ty_vmap ty_mmap) ty in
      mk_formula (ExTy (l, (tys, t), (subst_aux ~fix ty_vmap ty_mmap t_vmap t_mmap f_vmap f_mmap p)))

  let subst ?(fix=true)
      ?(ty_var_map=Subst.empty) ?(ty_meta_map=Subst.empty)
      ?(t_var_map=Subst.empty) ?(t_meta_map=Subst.empty)
      ?(f_var_map=Subst.empty) ?(f_meta_map=Subst.empty) f =
    if Subst.is_empty ty_var_map && Subst.is_empty ty_meta_map &&
       Subst.is_empty t_var_map && Subst.is_empty t_meta_map &&
       Subst.is_empty f_var_map && Subst.is_empty f_meta_map then
      f
    else
      subst_aux ~fix ty_var_map ty_meta_map t_var_map t_meta_map f_var_map f_meta_map f

  let free_args_inst ty_vmap t_vmap (ty_args, t_args) =
    (List.map (Ty.subst ~fix:false ty_vmap Subst.empty) ty_args,
     List.map (Term.subst ~fix:false ty_vmap Subst.empty t_vmap Subst.empty) t_args)

  let _empty = Subst.empty

  let partial_inst ty_vmap t_vmap f =
    let rec aux ty_vmap t_vmap f =
      match f.formula with
      | Not q -> neg (aux ty_vmap t_vmap q)
      | Ex (l, args, p) ->
        begin match List.filter (fun v -> not (Subst.Id.mem v t_vmap)) l with
          | [] -> aux ty_vmap t_vmap p
          | l' ->
            let l'', t_map = new_binder_subst ty_vmap _empty t_vmap [] l' in
            let q = subst_aux ~fix:false ty_vmap _empty t_map _empty _empty _empty p in
            let args' = free_args_inst ty_vmap t_map args in
            mk_formula (Ex (l'', args', q))
        end
      | All (l, args, p) ->
        begin match List.filter (fun v -> not (Subst.Id.mem v t_vmap)) l with
          | [] -> aux ty_vmap t_vmap p
          | l' ->
            let l'', t_map = new_binder_subst ty_vmap _empty t_vmap [] l' in
            let q = subst_aux ~fix:false ty_vmap _empty t_map _empty _empty _empty p in
            let args' = free_args_inst ty_vmap t_map args in
            mk_formula (All (l'', args', q))
        end
      | ExTy (l, args, p) ->
        begin match List.filter (fun v -> not (Subst.Id.mem v ty_vmap)) l with
          | [] -> aux ty_vmap t_vmap p
          | l' ->
            let q = subst_aux ~fix:false ty_vmap _empty t_vmap _empty _empty _empty p in
            let args' = free_args_inst ty_vmap t_vmap args in
            mk_formula (ExTy (l', args', q))
        end
      | AllTy (l, args, p) ->
        begin match List.filter (fun v -> not (Subst.Id.mem v ty_vmap)) l with
          | [] -> aux ty_vmap t_vmap p
          | l' ->
            let q = subst_aux ~fix:false ty_vmap _empty t_vmap _empty _empty _empty p in
            let args' = free_args_inst ty_vmap t_vmap args in
            mk_formula (AllTy (l', args', q))
        end
      | _ -> subst_aux ~fix:false ty_vmap _empty t_vmap _empty _empty _empty f
    in
    match f.formula with
    | Ex _ | All _
    | ExTy _ | AllTy _
    | Not { formula = (
          Ex _ | All _ |
          ExTy _ | AllTy _
        ) } ->
      aux ty_vmap t_vmap f
    | _ -> raise (Invalid_argument "Expr.partial_inst")

  let all l f =
    if l = [] then f else begin
      let vars, ft, f = match f.formula with
        | All (l', ft, f') ->
          let l'' = List.map Id.fresh l' in
          let subst =
            List.fold_left2 Subst.Id.bind Subst.empty
              l' (List.map Term.of_id l'')
          in
          l @ l'', ft, subst f'
        | _ ->
          let ft = fv (mk_formula (All (l, ([], []), f))) in
          l, to_free_args ft, f
      in
      Id.init_term_skolems vars ft;
      mk_formula (All (l, ft, f))
    end

  let allty l f =
    if l = [] then f else begin
      let l, f = match f.formula with
        | AllTy (l', _, f') -> l @ l', f'
        | _ -> l, f
      in
      let fv = fv (mk_formula (AllTy (l, ([], []), f))) in
      Id.init_ty_skolems l fv;
      mk_formula (AllTy (l, to_free_args fv, f))
    end

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
end

