
let section = Section.make "proof"

(* Pretty printing indications *)
(* ************************************************************************ *)

module Pretty = struct

  type assoc =
    | Left
    | Right

  type t = {
    infix   : bool;
    name    : string;
    assoc   : assoc option;
  }

  let mk ?assoc ?(infix=false) name = { infix; name; assoc; }

end

(* Proof terms *)
(* ************************************************************************ *)

type binder =
  | Pi
  | Arrow
  | Lambda
  | Forall
  | Exists

type id = t Expr.id

and descr =
  | Type
  | Id of id
  | App of t * t
  | Let of id * t * t
  | Binder of binder * id * t

and t = {
  ty : t;
  term : descr;
  mutable hash : int;
}

exception Function_expected of t
exception Type_mismatch of t * t

(* Std functions *)
(* ************************************************************************ *)

let rec hash_aux t =
  match t.term with
  | Type -> 0
  | Id x -> Expr.Id.hash x
  | App (f, arg) ->
    Hashtbl.hash (hash f, hash arg)
  | Let (x, v, body) ->
    Hashtbl.hash (Expr.Id.hash x, hash v, hash body)
  | Binder (b, var, body) ->
    Hashtbl.hash (Hashtbl.hash b, Expr.Id.hash var, hash body)

and hash t =
  if t.hash > 0 then t.hash
  else begin
    let h = hash_aux t in
    t.hash <- h;
    h
  end

let _descr = function
  | Type -> 0
  | Id _ -> 1
  | App _ -> 2
  | Let _ -> 3
  | Binder _ -> 4

let rec compare_aux t t' =
  match t.term, t'.term with
  | Type, Type -> 0
  | Id x, Id y -> Expr.Id.compare x y
  | App (f, arg), App (f', arg') ->
    CCOrd.Infix.(compare f f'
                 <?> (compare, arg, arg'))
  | Let (x, v, body), Let (x', v', body') ->
    CCOrd.Infix.(Expr.Id.compare x x'
                 <?> (compare, v, v')
                 <?> (compare, body, body'))
  | Binder (b, v, body), Binder (b', v', body') ->
    CCOrd.Infix.(Pervasives.compare b b'
                 <?> (Expr.Id.compare, v, v')
                 <?> (compare, body, body'))
  | u, v -> Pervasives.compare (_descr u) (_descr v)

and compare t t' =
  if t == t' then 0
  else
    CCOrd.(Pervasives.compare (hash t) (hash t')
           <?> (compare_aux, t, t'))

let equal t t' = compare t t' = 0


(* Bound variables *)
(* ************************************************************************ *)

module S = Set.Make(struct
    type nonrec t = t Expr.Id.t
    let compare = Expr.Id.compare
  end)

let rec free_vars acc t =
  match t.term with
  | Type -> acc
  | Id v -> S.add v acc
  | App (f, arg) ->
    free_vars (free_vars acc f) arg
  | Let (v, e, body) ->
    S.remove v (free_vars (free_vars acc e) body)
  | Binder (_, v, body) ->
    S.remove v (free_vars acc body)


(** Creating terms *)
let mk ty term =
  { ty; term; hash = -1; }

let const v = mk v.Expr.id_type (Id v)

let rec _Type = {
  ty = _Type;
  term = Type;
  hash = -1;
}

let _Prop =
  const @@ Expr.Id.mk_new "Prop" _Type

let letin v e body =
  if equal v.Expr.id_type e.ty then
    mk body.ty (Let (v, e, body))
  else
    raise (Type_mismatch (e, v.Expr.id_type))

let rec bind b v body =
  match b with
  | Lambda ->
    let fv = free_vars S.empty body.ty in
    let ty_b = if S.mem v fv then Pi else Arrow in
    let res_ty = bind ty_b v body.ty in
    mk res_ty (Binder (b, v, body))
  | Pi | Arrow ->
    mk _Type (Binder (b, v, body))
  | Forall | Exists ->
    if equal _Prop body.ty then
      mk _Prop (Binder (b, v, body))
    else
      raise (Type_mismatch (body, _Prop))


(* Typing and application *)
(* ************************************************************************ *)

module Subst = Map.Make(struct
    type nonrec t = t Expr.Id.t
    let compare = Expr.Id.compare
  end)

let extract_fun_ty t =
  match t.ty with
  | { term = Binder (Pi, v, ty) } -> v, ty
  | _ -> raise (Function_expected t)

let rec app t arg =
  let v, ty = extract_fun_ty t in
  let expected_arg_ty = v.Expr.id_type in
  let actual_arg_ty = arg.ty in
  if equal expected_arg_ty actual_arg_ty then
    let s = Subst.singleton v arg in
    let res_ty = subst s ty in
    mk res_ty (App (t, arg))
  else
    raise (Type_mismatch (arg, expected_arg_ty))

and subst s t =
  match t.term with
  | Type -> t
  | Id v ->
    begin try Subst.find v s
      with Not_found -> t end
  | App (f, arg) ->
    app (subst s f) (subst s arg)
  | Let (v, e, body) ->
    let e' = subst s e in
    let s' = Subst.remove v s in
    let v', s'' =
      if equal e.ty e'.ty then v, s'
      else
        let v' = Expr.Id.mk_new v.Expr.id_name e'.ty in
        v', Subst.add v (const v') s'
    in
    let body' = subst s'' body in
    if v == v' && e == e' && body == body' then t
    else letin v' e' body'
  | Binder (b, v, body) ->
    let ty = v.Expr.id_type in
    let ty' = subst s ty in
    let s' = Subst.remove v s in
    let v', s'' =
      if equal ty ty' then v, s'
      else
        let v' = Expr.Id.mk_new v.Expr.id_name ty' in
        v', Subst.add v (const v') s'
    in
    let body' = subst s'' body in
    if v == v' && body == body' then t
    else bind b v' body'


(* Shorthands for constructors *)
(* ************************************************************************ *)

let apply f l = List.fold_left app f l

let rec apply_left f = function
  | [] -> assert false
  | [x] -> x
  | x :: y :: r ->
    apply_left f (apply f [x; y] :: r)

let pi v body = bind Pi v body
let pis l body = List.fold_right pi l body

let lambda v body = bind Lambda v body
let lambdas l body = List.fold_right lambda l body

let arrow ty ret = bind Arrow (Expr.Id.mk_new "" ty) ret
let arrows l ret = List.fold_right arrow l ret

let forall v body = bind Forall v body
let foralls l body = List.fold_right forall l body

let exist v body = bind Exists v body
let exists l body = List.fold_right exist l body

(* Printing helpers *)
(* ************************************************************************ *)

let rec split_last = function
  | [] -> [], None
  | [x] -> [], Some x
  | x :: r ->
    let l, res = split_last r in
    x :: l, res


(* Term Uncurryfication *)
(* ************************************************************************ *)

let uncurry_app t =
  let rec aux acc = function
    | { term = App (f, arg) } ->
      aux (arg :: acc) f
    | t -> t, acc
  in
  aux [] t

let rec uncurry_assoc_left f = function
  | [] -> assert false
  | (x :: _) as l ->
    begin match uncurry_app x with
      | { term = Id f' }, l' when Expr.Id.equal f f' ->
        uncurry_assoc_left f (l' @ l)
      | _ -> l
    end

let rec uncurry_assoc_right f l =
  match split_last l with
  | _, None -> assert false
  | r, Some x ->
    begin match uncurry_app x with
      | { term = Id f' }, l' when Expr.Id.equal f f' ->
        r @ (uncurry_assoc_right f l')
      | _ -> l
    end

let uncurry ?tag t =
  match uncurry_app t with
  | ({ term = Id f } as f_t), l ->
    begin match CCOpt.(tag >>= (Expr.Id.get_tag f)) with
      | None -> `Prefix (f_t, l)
      | Some p ->
        let l =
          match p.Pretty.assoc with
          | None -> l
          | Some Pretty.Left -> uncurry_assoc_left f l
          | Some Pretty.Right -> uncurry_assoc_right f l
        in
        if p.Pretty.infix
        then `Infix (f_t, l)
        else `Prefix (f_t, l)
    end
  | (f_t, l) -> `Prefix (f_t, l)

(* Binder concatenation *)
(* ************************************************************************ *)

let flatten_binder b t =
  let rec aux b acc = function
    | { term = Binder (b', v, body) } when (b = b') ->
      aux b (v :: acc) body
    | t -> List.rev acc, t
  in
  aux b [] t

let concat_aux ty l acc =
  match l with
  | [] -> acc
  | _ -> (ty, List.rev l) :: acc

let concat_vars l =
  let rec aux ty acc curr = function
    | [] ->
      List.rev (concat_aux ty curr acc)
    | v :: r ->
      if equal ty v.Expr.id_type
      then aux ty acc (v :: curr) r
      else aux v.Expr.id_type (concat_aux ty curr acc) [v] r
  in
  aux _Type [] [] l

(* Binder printing helpers *)
(* ************************************************************************ *)

let binder_name = function
  | Pi -> "Π"
  | Arrow -> "->"
  | Lambda -> "λ"
  | Forall -> "∀"
  | Exists -> "∃"

let binder_sep = function _ -> ","

(* Printing *)
(* ************************************************************************ *)

let print_type fmt () =
  Format.fprintf fmt "Type"

let print_id fmt v =
  Expr.Id.print fmt v

let rec print_app fmt t =
  let f, l = uncurry_app t in
  assert (l <> []);
  Format.fprintf fmt "(%a@ %a)"
    print f CCFormat.(list ~sep:(return "@ ") print) l

and print_let fmt v e body =
  Format.fprintf fmt "@[<v>@[<hov>let %a =@ %a in@]@ %a@]"
    print_id v print e print body

and print_arrow fmt t =
  let l, body = flatten_binder Arrow t in
  let l' = List.map (fun v -> v.Expr.id_type) l in
  let sep fmt () = Format.fprintf fmt " ->@ " in
  Format.fprintf fmt "(@[<hov>%a@])" CCFormat.(list ~sep print) l'

and print_var_list fmt (ty, l) =
  assert (l <> []);
  Format.fprintf fmt "(%a :@ %a)"
    CCFormat.(list ~sep:(return "@ ") print_id) l print ty

and print_var_lists fmt l =
  CCFormat.(list ~sep:(return "@ ") print_var_list) fmt l

and print_binder fmt b t =
  let l, body = flatten_binder b t in
  let l' = concat_vars l in
  Format.fprintf fmt "(@[<hov 2>%s@[<hov>%a@]%s@ %a@])"
    (binder_name b) print_var_lists l'
    (binder_sep b) print body

and print fmt t =
  match t.term with
  | Type -> print_type fmt ()
  | Id v -> print_id fmt v
  | App _ -> print_app fmt t
  | Let (v, e, body) -> print_let fmt v e body
  | Binder (Arrow, _, _) -> print_arrow fmt t
  | Binder (b, _, _) -> print_binder fmt b t


(* Proof term constants *)
(* ************************************************************************ *)

let equal_id =
  let a_id = Expr.Id.mk_new "a" _Type in
  let a_type = const a_id in
  Expr.Id.mk_new "==" (pi a_id (arrows [a_type; a_type] _Prop))

let true_id = Expr.Id.mk_new "true" _Prop
let false_id = Expr.Id.mk_new "false" _Prop

let not_id = Expr.Id.mk_new "not" (arrow _Prop _Prop)

let imply_id =
  Expr.Id.mk_new "->" (arrows [_Prop; _Prop] _Prop)

let equiv_id =
  Expr.Id.mk_new "<->" (arrows [_Prop; _Prop] _Prop)

let or_id =
  Expr.Id.mk_new "||" (arrows [_Prop; _Prop] _Prop)

let and_id =
  Expr.Id.mk_new "&&" (arrows [_Prop; _Prop] _Prop)


let or_term = const or_id
let and_term = const and_id
let not_term = const not_id
let true_term = const true_id
let false_term = const false_id
let equal_term = const equal_id
let imply_term = const imply_id
let equiv_term = const equiv_id


(* Tanslating from Expr to Term *)
(* ************************************************************************ *)

let tr_tag = Tag.create ()

let of_id tr id =
  match Expr.Id.get_tag id tr_tag with
  | Some v -> v
  | None ->
    let ty = tr id.Expr.id_type in
    let v = Expr.Id.mk_new id.Expr.id_name ty in
    let () = Expr.Id.tag id tr_tag v in
    v

let of_function_descr tr tr' fd =
  let rec aux_vars body = function
    | [] -> body
    | v :: r -> aux_vars (pi (of_id tr v) body) r
  and aux_args vars body = function
    | [] -> aux_vars body vars
    | ty :: r -> aux_args vars (arrow (tr' ty) body) r
  in
  aux_args
    (List.rev fd.Expr.fun_vars)
    (tr' fd.Expr.fun_ret)
    (List.rev fd.Expr.fun_args)

let of_unit _ = assert false

let of_ttype Expr.Type = _Type

let of_ty =
  CCCache.with_cache_rec
    (CCCache.lru ~eq:Expr.Ty.equal ~hash:Expr.Ty.hash 4013)
    (fun of_ty ty -> match ty with
       | { Expr.ty = Expr.TyVar v } -> const @@ of_id of_ttype v
       | { Expr.ty = Expr.TyMeta m } -> of_ty Synth.ty
       | { Expr.ty = Expr.TyApp (f, l) } ->
         let f' = of_id (of_function_descr of_unit of_ttype) f in
         let l' = List.map of_ty l in
         apply (const f') l'
    )

let rec of_term =
  CCCache.with_cache_rec
    (CCCache.lru ~eq:Expr.Term.equal ~hash:Expr.Term.hash 4013)
    (fun of_term t -> match t with
       | { Expr.term = Expr.Var v } -> const @@ of_id of_ty v
       | { Expr.term = Expr.Meta m } -> of_term @@ Synth.term Expr.(m.meta_id.id_type)
       | { Expr.term = Expr.App (f, tys, args) } ->
         let f' = of_id (of_function_descr of_ttype of_ty) f in
         let tys' = List.map of_ty tys in
         let args' = List.map of_term args in
         apply (apply (const f') tys') args'
    )

let f_tag = Tag.create ()

let rec of_formula f =
  match Expr.Formula.get_tag f f_tag with
  | Some t -> t
  | None ->
    let t = of_formula_aux f in
    Expr.Formula.tag f f_tag t;
    t

and of_formula_aux f =
  match f.Expr.formula with
  | Expr.True -> true_term
  | Expr.False -> false_term
  | Expr.Pred p ->
    of_term p
  | Expr.Equal (x, y) ->
    let x' = of_term x in
    let y' = of_term y in
    apply equal_term [x'.ty; x'; y']

  | Expr.Not f' ->
    app not_term (of_formula f')
  | Expr.Imply (p, q) ->
    apply imply_term [of_formula p; of_formula q]
  | Expr.Equiv (p, q) ->
    apply equiv_term [of_formula p; of_formula q]

  | Expr.Or _ ->
    let order = CCOpt.get_exn @@ Expr.Formula.get_tag f Expr.f_order in
    of_tree or_term order
  | Expr.And l ->
    let order = CCOpt.get_exn @@ Expr.Formula.get_tag f Expr.f_order in
    of_tree and_term order

  | Expr.All (l, _, body) ->
    foralls (List.map (of_id of_ty) l) (of_formula body)
  | Expr.AllTy (l, _, body) ->
    foralls (List.map (of_id of_ttype) l) (of_formula body)

  | Expr.Ex (l, _, body) ->
    exists (List.map (of_id of_ty) l) (of_formula body)
  | Expr.ExTy (l, _, body) ->
    exists (List.map (of_id of_ttype) l) (of_formula body)

and of_tree t = function
  | Expr.F f -> of_formula f
  | Expr.L l -> apply_left t @@ List.map (of_tree t) l



