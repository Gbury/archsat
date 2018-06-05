
let section = Section.make "proof"

(* Proof terms *)
(* ************************************************************************ *)

module S = Expr.Subst

type binder =
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
  mutable reduced : t option;
  mutable free : (id, unit) S.t option;
}


exception Function_expected of t
exception Type_mismatch of t * t
exception Match_Impossible of t * t
exception Unif_Impossible of t * t

(* Small helper *)
(* ************************************************************************ *)

let _descr = function
  | Type -> 0
  | Id _ -> 1
  | App _ -> 2
  | Let _ -> 3
  | Binder _ -> 4

(* Binder printing helpers *)
(* ************************************************************************ *)

let binder_name = function
  | Lambda -> "λ"
  | Forall -> "∀"
  | Exists -> "∃"

let binder_sep = function _ -> ","

(* Debug printing *)
(* ************************************************************************ *)

let rec pp fmt t =
  match t.term with
  | Type -> Format.fprintf fmt "Type"
  | Id v -> Expr.Id.print fmt v
  | App (f, arg) ->
    Format.fprintf fmt "@[<hv 2>(%a@ %a)@]" pp f pp arg
  | Let (v, e, body) ->
    Format.fprintf fmt "@[<v>let %a = %a in@ @]%a"
      Expr.Id.print v pp e pp body
  | Binder (b, v, body) ->
    Format.fprintf fmt "@[<hv 2>%s %a.@ %a@]"
      (binder_name b) Expr.Id.print v pp body

(* Id creation *)
(* ************************************************************************ *)

let var_tag = Tag.create ()

let is_var v =
  match Expr.Id.get_tag v var_tag with
  | None -> false
  | Some () -> true

let var s ty =
  let tags = Tag.add Tag.empty var_tag () in
  Expr.Id.mk_new ~tags s ty

let declare s ty = Expr.Id.mk_new s ty

type Expr.builtin += Defined of t

let define s def =
  Expr.Id.mk_new ~builtin:(Defined def) s def.ty

(* Free variables *)
(* ************************************************************************ *)

let merge s s' = S.merge (fun _ o o' -> CCOpt.(o <+> o')) s s'

let rec free_vars t =
  match t.free with
  | Some s -> s
  | None ->
    let res =
      match t.term with
      | Type -> S.empty
      | Id v -> S.Id.bind S.empty v ()
      | App (f, arg) -> merge (free_vars f) (free_vars arg)
      | Binder (_, v, body) -> S.Id.remove v (free_vars body)
      | Let (v, e, body) -> S.Id.remove v (merge (free_vars e) (free_vars body))
    in
    t.free <- Some res;
    res

let occurs v t = S.Id.mem v (free_vars t)

(* Simple Term creation *)
(* ************************************************************************ *)

(** Creating terms *)
let mk ty term =
  { ty; term; hash = -1; free = None; reduced = None; }

let id v = mk v.Expr.id_type (Id v)

let rec _Type = {
  ty      = _Type;
  term    = Type;
  hash    = 13; (* TODO: better base hash ? *)
  free    = None;
  reduced = Some _Type;
}

let _Prop_id = declare "Prop" _Type
let _Prop = id _Prop_id

(* Reduction and comparison *)
(* ************************************************************************ *)

(* get a function type *)
let extract_fun_ty t =
  match t.ty with
  | { term = Binder (Forall, v, ty) } -> v, ty
  | _ -> raise (Function_expected t)

(* function application *)
let rec _assert t ty =
  if not (equal t.ty ty) then begin
    Util.error
      "@[<hv>Proof term@ %a@ has type@ %a@ but was expected of type@ %a"
      pp t pp t.ty pp ty;
    raise (Type_mismatch (t, ty))
  end

and app t arg =
  let v, ty = extract_fun_ty t in
  let expected_arg_ty = v.Expr.id_type in
  _assert arg expected_arg_ty;
  let s = S.Id.bind S.empty v arg in
  let res_ty = subst s ty in
  mk res_ty (App (t, arg))

and letin v e body =
  assert (is_var v);
  _assert e v.Expr.id_type;
  mk body.ty (Let (v, e, body))

and bind b v body =
  assert (is_var v);
  match b with
  | Lambda ->
    let res_ty = bind Forall v body.ty in
    mk res_ty (Binder (Lambda, v, body))
  | Forall | Exists ->
    mk _Prop (Binder (b, v, body))

and subst s t =
  match t.term with
  | Type -> t
  | Id v ->
    begin try S.Id.get v s
      with Not_found -> t end
  | App (f, arg) ->
    app (subst s f) (subst s arg)
  | Let (v, e, body) ->
    let e' = subst s e in
    let s' = S.Id.remove v s in
    let v', s'' =
      if equal e.ty e'.ty then v, s'
      else
        let v' = var v.Expr.id_name e'.ty in
        v', S.Id.bind s' v (id v')
    in
    let body' = subst s'' body in
    if v == v' && e == e' && body == body' then t
    else mk body'.ty (Let (v', e', body'))
  | Binder (b, v, body) ->
    let ty = v.Expr.id_type in
    let ty' = subst s ty in
    let s' = S.Id.remove v s in
    let v', s'' =
      if equal ty ty' then v, s'
      else
        let v' = var v.Expr.id_name ty' in
        v', S.Id.bind s' v (id v')
    in
    let body' = subst s'' body in
    if v == v' && body == body' then t
    else bind b v' body'

and reduce_aux t =
  match t.term with
  | Type -> t
  | Id { Expr.builtin = Defined b; _ } -> b
  | Id _ -> t
  | App (f, arg) ->
    let f' = reduce f in
    if f == f' then begin (* f is already reduced *)
      let arg' = reduce arg in
      if arg == arg' then begin (* arg is already reduced *)
        match f.term with
        | Binder (Lambda, v, body) ->
          let body' = reduce body in
          reduce (subst (S.Id.bind S.empty v arg) body')
        | _ -> t
      end else
        reduce (app f arg') (* recompute the type just to be sure *)
    end else
      reduce (app f' arg)
  | Let (v, e, body) ->
    let e' = reduce e in
    let body' = reduce body in
    reduce (subst (S.Id.bind S.empty v e') body')
  | Binder (b, v, body) ->
    let body' = reduce body in
    if body == body' then t else bind b v body'

and reduce t =
  match t.reduced with
  | Some t' -> t'
  | None ->
    let t' = reduce_aux t in
    t'.reduced <- Some t';
    t.reduced <- Some t';
    t'

and compare_rec t t' =
  match t.term, t'.term with
  | Type, Type -> 0
  | Id x, Id y -> Expr.Id.compare x y
  | App (f, arg), App (f', arg') ->
    CCOrd.Infix.(compare_aux f f'
                 <?> (compare_aux, arg, arg'))
  | Let (x, v, body), Let (x', v', body') ->
    CCOrd.Infix.(Expr.Id.compare x x'
                 <?> (compare_aux, v, v')
                 <?> (compare_aux, body, body'))
  | Binder (b, v, body), Binder (b', v', body') ->
    CCOrd.Infix.(Pervasives.compare b b'
                 <?> (Expr.Id.compare, v, v')
                 <?> (compare_aux, body, body'))
  | u, v -> Pervasives.compare (_descr u) (_descr v)

and compare_aux t t' =
  if t == t' then 0
  else
    CCOrd.(Pervasives.compare (hash t) (hash t')
           <?> (compare_rec, t, t'))

and compare t t' =
  compare_aux (reduce t) (reduce t')

and equal t t' =
  compare t t' = 0

and hash_id id = hash id.Expr.id_type

and hash_aux t =
  match t.term with
  | Type -> 0
  | Id x -> hash_id x
  | App (f, arg) ->
    Hashtbl.hash (hash f, hash arg)
  | Let (x, v, body) ->
    Hashtbl.hash (hash_id x, hash v, hash body)
  | Binder (b, var, body) ->
    Hashtbl.hash (Hashtbl.hash b, hash_id var, hash body)

and hash t =
  if t.hash > 0 then t.hash
  else begin
    let h = hash_aux (reduce t) in
    t.hash <- h;
    h
  end


(* Unification *)
(* ************************************************************************ *)
(*
let rec follow subst = function
  | { term = Id v } as t ->
    begin match S.Id.get v subst with
      | exception Not_found -> t
      | t' ->follow subst  t'
    end
  | t -> t

let rec occurs_check subst l = function
  | { term = Type } -> false
  | { term = Id v } ->
    CCList.mem ~eq:Expr.Id.equal v l ||
    begin match S.Id.get v subst with
      | exception Not_found -> false
      | e -> occurs_check subst (v :: l) e
    end
  | { term = App (f, arg) } -> occurs_check subst l f || occurs_check subst l arg
  | { term = Let (_, e, body) } -> occurs_check subst l e || occurs_check subst l body
  | { term = Binder (_, _, body) } -> occurs_check subst l body

let rec unif_aux subst s t =
  let s = follow subst s in
  let t = follow subst t in
  match s, t with
   (* TODO/WARNING: check that v is a variable *)
  | ({ term = Id v } as m), u
  | u, ({ term = Id v } as m) ->
    if equal m u then subst
    else if occurs_check subst [v] u then raise (Unif_Impossible (m, u))
    else S.Id.bind subst v u
  | { term = Type },
    { term = Type } -> subst
  | { term = App (f, arg) },
    { term = App (f', arg') } ->
    unif_aux (unif_aux subst f f') arg arg'
  | { term = Binder (b, v, body) },
    { term = Binder (b', v', body') } ->
    if b = b' then
      unif_aux (S.Id.bind subst v (id v')) body body'
    else
      raise (Unif_Impossible (s, t))
  | _ -> raise (Unif_Impossible (s, t))

let unif s t =
  let res = unif_aux S.empty s t in
  let fv = merge (free_vars s) (free_vars t) in
  S.filter (fun v _ -> S.Id.mem v fv) res
*)

(* Shorthands for constructors *)
(* ************************************************************************ *)

let apply f l = List.fold_left app f l

let rec apply_left f = function
  | [] -> assert false
  | [x] -> x
  | x :: y :: r ->
    apply_left f (apply f [x; y] :: r)

let lambda v body = bind Lambda v body
let lambdas l body = List.fold_right lambda l body

let arrow ty ret = bind Forall (var "_" ty) ret
let arrows l ret = List.fold_right arrow l ret

let forall v body = bind Forall v body
let foralls l body = List.fold_right forall l body

let exist v body = bind Exists v body
let exists l body = List.fold_right exist l body

(* Proof term constants *)
(* ************************************************************************ *)

let true_id = declare "true" _Prop
let true_term = id true_id

let false_id = declare "false" _Prop
let false_term = id false_id

let imply_id =
  let a = var "A" _Prop in
  let b = var "B" _Prop in
  let t = lambda a (lambda b (arrow (id a) (id b))) in
  define "imply" t

let imply_term = id imply_id

let not_id =
  let a = var "A" _Prop in
  let t = lambda a (apply imply_term [id a; false_term]) in
  define "not" t

let not_term = id not_id

let equal_id =
  let a_id = var "a" _Type in
  let a_type = id a_id in
  declare "==" (forall a_id (arrows [a_type; a_type] _Prop))

let equal_term = id equal_id

let or_id =
  declare "||" (arrows [_Prop; _Prop] _Prop)

let or_term = id or_id

let and_id =
  declare "&&" (arrows [_Prop; _Prop] _Prop)

let and_term = id and_id

let equiv_id =
  let a = var "A" _Prop in
  let b = var "B" _Prop in
  let t_a = id a in
  let t_b = id b in
  let t = lambda a (lambda b (
      apply and_term [
        apply imply_term [t_a; t_b];
        apply imply_term [t_b; t_a];
      ]
    )) in
  define "iff" t

let equiv_term = id equiv_id

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
  | (x :: l) as res ->
    begin match uncurry_app x with
      | { term = Id f' }, l' when Expr.Id.equal f f' ->
        uncurry_assoc_left f (l' @ l)
      | _ -> res
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

let uncurry ?assoc t =
  match uncurry_app t with
  | ({ term = Id f } as f_t), l ->
    let l = CCOpt.(
        map_or ~default:l (function
            | Pretty.Left -> uncurry_assoc_left f l
            | Pretty.Right -> uncurry_assoc_right f l)
          (assoc >>= Expr.Id.get_tag f)
      ) in
    (f_t, l)
  | (f_t, l) -> (f_t, l)

(* Binder concatenation *)
(* ************************************************************************ *)

let flatten_binder o b t =
  let rec aux b acc = function
    | { term = Binder (b', v, body) } when (b = b') && o = occurs v body ->
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
  let l, body = flatten_binder false Forall t in
  let l' = List.map (fun v -> v.Expr.id_type) l in
  let sep fmt () = Format.fprintf fmt " ->@ " in
  Format.fprintf fmt "(@[<hov>%a ->@ %a@])"
    CCFormat.(list ~sep print) l' print body

and print_var_list fmt (ty, l) =
  assert (l <> []);
  Format.fprintf fmt "(%a :@ %a)"
    CCFormat.(list ~sep:(return "@ ") print_id) l print ty

and print_var_lists fmt l =
  CCFormat.(list ~sep:(return "@ ") print_var_list) fmt l

and print_binder fmt b t =
  let l, body = flatten_binder true b t in
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
  | Binder (Forall, v, body) -> print_arrow fmt t
  | Binder (b, _, _) -> print_binder fmt b t

let print_typed fmt t =
  Format.fprintf fmt "@[<hv 2>%a :@ %a@]" print t print t.ty

(* Pattern matching *)
(* ************************************************************************ *)

let rec match_aux subst pat t =
  match pat, t with
  | { term = Id v }, _ when is_var v ->
    begin match S.Id.get v subst with
      | exception Not_found -> S.Id.bind subst v t
      | t' ->
        if equal t t' then subst
        else raise (Match_Impossible (pat, t))
    end
  | { term = Type },
    { term = Type } ->
    subst
  | { term = Id v },
    { term = Id v' } ->
    if Expr.Id.equal v v' then subst
    else raise (Match_Impossible (pat, t))
  | { term = App (f, f_arg) },
    { term = App (g, g_arg) } ->
    match_aux (match_aux subst f g) f_arg g_arg
  | { term = Binder (b, v, body) },
    { term = Binder (b', v', body') } ->
    if b = b' then
      match_aux (S.Id.bind subst v (id v')) body body'
    else
      raise (Match_Impossible (pat, t))
  | _ -> raise (Match_Impossible (pat, t))

let pmatch ~pat t =
  (* Util.debug ~section "@[<hv 2>pattern match:@ %a@ ~~~@ %a" print pat print t; *)
  let s = match_aux S.empty (reduce pat) (reduce t) in
  let fv = free_vars pat in
  S.filter (fun v _ -> S.Id.mem v fv) s

(* Tanslating from Expr to Term *)
(* ************************************************************************ *)

module Hty = Hashtbl.Make(Expr.Ty)
module Hterm = Hashtbl.Make(Expr.Term)

(* Translation caches *)
let tr_tag = Tag.create ()          (** ids are unique, so storing cache in tags is safe *)
let ty_cache = Hty.create 4013      (** Types and terms are not unique/hashconsed, *)
let term_cache = Hterm.create 4013  (** so we need a table instead of tags *)
let f_tag = Tag.create ()           (** Formula translation need to get into account
                                        the creation roder (stored in the order tag, which
                                        is ignored when comparing formulas), so a hashtable
                                        cannot be used, hence the tag for caching. *)

(* Callback for inferred identifiers *)
type callback = id -> unit
type 'a translator = ?callback:callback -> 'a -> t

(** Traps force translation of given types and terms *)
let trap_id key v =
  Util.debug ~section "id translation: %a --> %a"
    Expr.Print.id key Expr.Print.id v;
  Expr.Id.tag key tr_tag v

let trap_ty key v =
  Util.debug ~section "trap: %a --> %a"
    Expr.Print.ty key print v;
  Hty.add ty_cache key v

let trap_term key v =
  Util.debug ~section "trap: %a --> %a"
    Expr.Print.term key print v;
  Hterm.add term_cache key v

(* Id translation *)
let of_id_aux mk tr ?callback id =
  (* Util.debug ~section "translate id: %a" Expr.Print.id id; *)
  match Expr.Id.get_tag id tr_tag with
  | Some v ->
    (* Util.debug ~section "cached value: %a" Expr.Print.id v; *)
    v
  | None ->
    let ty = tr ?callback id.Expr.id_type in
    let v = mk id.Expr.id_name ty in
    let () = Expr.Id.tag id tr_tag v in
    let () = match callback with Some f -> f v | None -> () in
    (* Util.debug ~section "new cached id: %a" Expr.Print.id v; *)
    v

let of_id mk tr ?callback v = id (of_id_aux var tr ?callback v)

let of_function_descr tr tr' ?callback fd =
  let rec aux_vars body = function
    | [] -> body
    | v :: r -> aux_vars (forall (of_id_aux ?callback var tr v) body) r
  and aux_args vars body = function
    | [] -> aux_vars body vars
    | ty :: r -> aux_args vars (arrow (tr' ?callback ty) body) r
  in
  aux_args
    (List.rev fd.Expr.fun_vars)
    (tr' ?callback fd.Expr.fun_ret)
    (List.rev fd.Expr.fun_args)

(* Base cases for translation. *)
let of_unit ?callback _ = assert false

let of_ttype ?callback Expr.Type = _Type

(* Type translation *)
let rec of_ty_aux ?callback = function
  | ty when Expr.Ty.equal Expr.Ty.prop ty ->
    (* TODO: emit implicit declaration of $o *)
    _Prop
  | { Expr.ty = Expr.TyVar v } -> of_id var ?callback of_ttype v
  | { Expr.ty = Expr.TyMeta m } -> of_ty Synth.ty
  | { Expr.ty = Expr.TyApp (f, l) } ->
    let f' = of_id declare ?callback (of_function_descr of_unit of_ttype) f in
    let l' = List.map of_ty l in
    apply f' l'

and of_ty ?callback ty =
  (* Util.debug ~section "translate ty: %a" Expr.Print.ty ty; *)
  match Hty.find ty_cache ty with
  | res ->
    Util.debug ~section "cached value: %a" print res;
    res
  | exception Not_found ->
    let res = of_ty_aux ?callback ty in
    let () = Hty.add ty_cache ty res in
    Util.debug ~section "new cached ty: %a" print res;
    res

(* Term translation *)
let rec of_term_aux ?callback = function
  | { Expr.term = Expr.Var v } ->
    of_id var ?callback of_ty v
  | { Expr.term = Expr.Meta m } ->
    of_term ?callback (Synth.term Expr.(m.meta_id.id_type))
  | { Expr.term = Expr.App (f, tys, args) } ->
    let f' = of_id declare ?callback (of_function_descr of_ttype of_ty) f in
    let tys' = List.map (of_ty ?callback) tys in
    let args' = List.map (of_term ?callback) args in
    apply (apply f' tys') args'

and of_term ?callback t =
  (* Util.debug ~section "translate term: %a" Expr.Print.term t; *)
  match Hterm.find term_cache t with
  | res ->
    (* Util.debug ~section "cached result: %a" print res; *)
    res
  | exception Not_found ->
    let res = of_term_aux ?callback t in
    let () = Hterm.add term_cache t res in
    (* Util.debug ~section "new cached term: %a" print res; *)
    res

(* Formula translation *)
let rec of_formula ?callback f =
  (* Util.debug ~section "translate formula: %a" Expr.Print.formula f; *)
  match Expr.Formula.get_tag f f_tag with
  | Some t ->
    (* Util.debug ~section "cached result: %a" print t; *)
    t
  | None ->
    let t = of_formula_aux ?callback f in
    Expr.Formula.tag f f_tag t;
    (* Util.debug ~section "new cached formula: %a" print t; *)
    t

and of_formula_aux ?callback f =
  match f.Expr.formula with
  | Expr.True -> true_term
  | Expr.False -> false_term
  | Expr.Pred p ->
    of_term ?callback p
  | Expr.Equal (x, y) ->
    let x' = of_term ?callback x in
    let y' = of_term ?callback y in
    let ty = x'.ty in
    let a, b =
      match CCOpt.get_exn @@ Expr.Formula.get_tag f Expr.t_order with
      | Expr.Same -> x', y'
      | Expr.Inverse -> y', x'
    in
    apply equal_term [ty; a; b]

  | Expr.Not f' ->
    app not_term (of_formula ?callback f')
  | Expr.Imply (p, q) ->
    apply imply_term [of_formula ?callback p; of_formula ?callback q]
  | Expr.Equiv (p, q) ->
    apply equiv_term [of_formula ?callback p; of_formula ?callback q]

  | Expr.Or _ ->
    let order = CCOpt.get_exn @@ Expr.Formula.get_tag f Expr.f_order in
    of_tree ?callback or_term order
  | Expr.And l ->
    let order = CCOpt.get_exn @@ Expr.Formula.get_tag f Expr.f_order in
    of_tree ?callback and_term order

  | Expr.All ((tys, ts), _, body) ->
    foralls (List.map (of_id_aux var ?callback of_ttype) tys) @@
    foralls (List.map (of_id_aux var ?callback of_ty) ts) (of_formula ?callback body)
  | Expr.Ex ((tys, ts), _, body) ->
    exists (List.map (of_id_aux var ?callback of_ttype) tys) @@
    exists (List.map (of_id_aux var ?callback of_ty) ts) (of_formula ?callback body)

and of_tree ?callback t = function
  | Expr.F f -> of_formula ?callback f
  | Expr.L l -> apply_left t @@ List.map (of_tree ?callback t) l



