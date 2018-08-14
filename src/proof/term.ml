
let section = Section.make "term"

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
  hash : int;
  index : int;
  term : descr;
  reduced : t Lazy.t;
  free : (id, unit) S.t;
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

(* Debug printing *)
(* ************************************************************************ *)

let binder_name = function
  | Lambda -> "λ"
  | Forall -> "∀"
  | Exists -> "∃"

let binder_sep = function _ -> ","

let rec pp fmt t = pp_descr fmt t.term

and pp_descr fmt = function
  | Type -> Format.fprintf fmt "Type"
  | Id v -> Expr.Id.print fmt v
  | App (f, arg) ->
    Format.fprintf fmt "@[<hv 2>(%a@ %a)@]" pp f pp arg
  | Let (v, e, body) ->
    Format.fprintf fmt "@[<v>let %a = %a in@ @]%a"
      Expr.Id.print v pp e pp body
  | Binder (b, v, body) ->
    Format.fprintf fmt "@[<hv 2>(%s (%a : %a).@ %a)@]"
      (binder_name b) Expr.Id.print v pp v.Expr.id_type pp body

let pp fmt t =
  Format.fprintf fmt "[%d.%d] %a" t.index t.hash pp t

(* Std operations on terms *)
(* ************************************************************************ *)

let hash t = t.hash
let compare t t' = Pervasives.compare t.index t'.index
let equal t t' = compare t t' = 0

let ty t = t.ty
let free_vars t = t.free
let reduce t = Lazy.force t.reduced
let is_reduced t = t == (reduce t)

module Aux = struct
  type nonrec t = t
  let hash = hash
  let compare = compare
  let equal = equal
end

module Reduced = struct

  type nonrec t = t

  let hash t = hash @@ reduce t

  let compare t t' =
    if Aux.equal t t' then 0
    else Aux.compare (reduce t) (reduce t')

  let equal t t' = compare t t' = 0
end

module Hs = Hashtbl.Make(Aux)

(* Id creation *)
(* ************************************************************************ *)

let contract_tag = Tag.create ()

type Expr.builtin +=
  | Var
  | Declared
  | Defined of t

let is_var v =
  match v.Expr.builtin with
  | Var -> true
  | _ -> false

let var s ty =
  Expr.Id.mk_new ~builtin:Var s ty

let var_typed v ty =
  let s = v.Expr.id_name in
  let tags = ref (! (v.Expr.id_tags)) in
  Expr.Id.mk_new ~tags ~builtin:Var s ty

let declare s ty =
  Expr.Id.mk_new ~builtin:Declared s ty

let definitions = Hs.create 17

let define s def =
  let v = Expr.Id.mk_new ~builtin:(Defined def) s def.ty in
  Hs.add definitions def v;
  Hs.add definitions (reduce def) v;
  v

(* Free variables computing *)
(* ************************************************************************ *)

let merge s s' = S.merge (fun _ o o' -> CCOpt.(o <+> o')) s s'

let compute_free_vars = function
  | Type -> S.empty
  | Id v ->
    let s = free_vars v.Expr.id_type in
    if is_var v then S.Id.bind s v () else s
  | App (f, arg) ->
    merge (free_vars f) (free_vars arg)
  | Binder (_, v, body) ->
    S.Id.remove v (merge (free_vars v.Expr.id_type) (free_vars body))
  | Let (v, e, body) ->
    S.Id.remove v (merge (free_vars e) (free_vars body))

let occurs v t = S.Id.mem v (free_vars t)
let not_occurs v t = not (occurs v t)

(* Hash computing *)
(* ************************************************************************ *)

let hash_type = 3
let hash_id = 5
let hash_app = 7
let hash_let = 9
let hash_binder = 13

let compute_hash = function
  | Type -> hash_type
  | Id v ->
    CCHash.(pair int) hash (hash_id, v.Expr.id_type)
  | App (f, arg) ->
    CCHash.(triple int) hash hash (hash_app, f, arg)
  | Let (v, e, body) ->
    CCHash.(triple int) hash hash (hash_let, e, body)
  | Binder (b, v, body) ->
    CCHash.(triple int) hash hash (hash_binder, v.Expr.id_type, body)


(* Alpha-equivalence *)
(* ************************************************************************ *)

let alpha_compatible_subst fv subst =
  S.for_all (fun v () ->
      match S.Id.get v subst with
      | v' -> Expr.Id.equal v v'
      | exception Not_found -> true
    ) fv

let rec compare_alpha subst pat t =
  if pat == t then begin
    let fv = free_vars pat in
    if alpha_compatible_subst fv subst then ()
    else raise (Match_Impossible (pat, t))
  end else match pat, t with
  | { term = Id v }, { term = Id v' } ->
    begin match S.Id.get v subst with
      | exception Not_found ->
        (** TODO: what to do with free variables ? *)
        if Expr.Id.equal v v' then ()
        else raise (Match_Impossible (pat, t))
      | v'' ->
        if Expr.Id.equal v'' v' then ()
        else raise (Match_Impossible (pat, t))
    end
  | { term = Type },
    { term = Type } -> ()
  | { term = App (f, f_arg) },
    { term = App (g, g_arg) } ->
    compare_alpha subst f g;
    compare_alpha subst f_arg g_arg
  | { term = Binder (b, v, body) },
    { term = Binder (b', v', body') } ->
    if b = b' then begin
      compare_alpha subst v.Expr.id_type v'.Expr.id_type;
      compare_alpha (S.Id.bind subst v v') body body'
    end else
      raise (Match_Impossible (pat, t))
  | { term = Let (v, e, body) },
    { term = Let (v', e', body') } ->
    (** Hypothesis: is e and e' are alpha-equivalent, then their type also are. *)
    compare_alpha subst e e';
    compare_alpha (S.Id.bind subst v v') body body'
  | _ -> raise (Match_Impossible (pat, t))

let alpha t t' =
  match compare_alpha S.empty t t' with
  | () -> true
  | exception Match_Impossible _ -> false

(* Hashconsed set *)
(* ************************************************************************ *)

module H = Weak.Make(struct

    type nonrec t = t

    let hash = hash

    (** In our case, only the first constructor of a term can be not hashconsed,
        which means that for any term that is not [t] or [t'], equality modulo
        alpha renaming can be decided using physical equality *)
    let equal t t' =
      match t, t' with
      | { term = Type }, { term = Type } -> true
      | { term = Id v }, { term = Id v' } -> Expr.Id.equal v v'
      | { term = App (f, f_arg) },
        { term = App (g, g_arg) } -> f == g && f_arg == g_arg
      | { term = Binder (b, v, body) },
        { term = Binder (b', v', body') } ->
        (b = b' && v == v' && body == body') || alpha t t'
      | { term = Let _ },
        { term = Let _ }
        -> alpha t t'
      | _, _ -> false

  end)

let idx_terms = ref 0
let all_terms = H.create 99997

(** The cyclic Type constant is a special case that must be done by
    hand since it is its own type. *)
let rec _Type = {
  index   = 0;
  ty      = _Type;
  term    = Type;
  reduced = lazy _Type;
  hash    = 13; (* TODO: better base hash ? *)
  free    = S.empty;
}

(** Register the constant in the weak hashtbl *)
let () = H.add all_terms _Type


(** Create hashconsed terms *)

let mk_reduced ty term =
  (** First create a simplified term, wiht only the bare minimum information
      to check whether it alreayd exists in the weak hashtbl. *)
  incr idx_terms;
  let hash = compute_hash term in
  let rec t = {
    ty; term; hash;
    index = !idx_terms;
    reduced = lazy t;
    free = compute_free_vars term;
  } in
  H.merge all_terms t

let mk_normal ty term reduced =
  (* Format.eprintf "mk_normal: @[<v>ty: %a@ descr: %a@ reduced: %a@]@."
     pp ty pp_descr term pp reduced; *)
  (*
  if not (is_reduced reduced) then begin
    Util.error ~section "@[<hv>Term@ %a@ reduced from@ %a@ is not in normal form !@]"
      pp reduced pp_descr term;
    assert false
  end;
  *)
  (* assert (equal (reduce ty) (reduce reduced.ty)); *)
  incr idx_terms;
  let hash = compute_hash term in
  let t = {
    ty; term; hash; reduced;
    index = !idx_terms;
    free = compute_free_vars term;
  } in
  H.merge all_terms t

(* Creating simple terms (i.e no application or let-binding) *)
(* ************************************************************************ *)

let id v =
  let t = Id v in
  let ty = v.Expr.id_type in
  match v.Expr.builtin with
  | Var | Declared -> mk_reduced ty t
  | Defined t' -> mk_normal ty t (lazy (reduce t'))
  (** Variables should have one of these as builtins *)
  | _ -> assert false

let _Prop_id = declare "Prop" _Type
let _Prop = id _Prop_id


(* Reduction and comparison *)
(* ************************************************************************ *)

(* get a function type *)
let extract_fun_ty t =
  match reduce (ty t) with
  | { term = Binder (Forall, v, ty) } -> v, ty
  | _ ->
    Util.error ~section
      "@[<v 2>Trying to extract function type fom:@ term: %a@ ty: %a@ reduced ty: %a"
      pp t pp (ty t) pp (reduce (ty t));
    raise (Function_expected t)

(* equality assertion *)
let _assert t t_ty =
  if not (Reduced.equal (ty t) t_ty) then begin
    Util.error
      "@[<hv>Proof term@ %a@ has type@ %a@ but was expected of type@ %a"
      pp t pp (reduce (ty t)) pp (reduce t_ty);
    raise (Type_mismatch (t, t_ty))
  end

(* function application *)
let rec app f arg =
  (* Format.eprintf "app: @[<hv>%a@ @@@ %a@]@." pp f pp arg; *)
  let t = App (f, arg) in
  let v, ty = extract_fun_ty f in
  let expected_arg_ty = v.Expr.id_type in
  _assert arg expected_arg_ty;
  let s = S.Id.bind S.empty v arg in
  let res_ty = subst s ty in
  (* check for normal forms *)
  match f with
  | { term = Binder (Lambda, v, body) } ->
    (* Format.eprintf "reducing beta-redex@."; *)
    let reduced = lazy (reduce_beta v arg body) in
    (* Format.eprintf "beta-redex reduced: @[<hov>%a@]@." pp reduced; *)
    mk_normal res_ty t reduced
  | _ ->
    (* Format.eprintf "not a beta-redex@."; *)
    if is_reduced f && is_reduced arg then
      mk_reduced res_ty t
    else begin
      let reduced = lazy (reduce (app (reduce f) (reduce arg))) in
      mk_normal res_ty t reduced
    end

and letin v e body =
  assert (is_var v);
  _assert e v.Expr.id_type;
  let reduced = lazy (reduce_beta v e body) in
  mk_normal (ty body) (Let (v, e, body)) reduced

and bind b v body =
  assert (is_var v);
  let t = Binder (b, v, body) in
  let ty =
    match b with
    | Lambda -> bind Forall v (ty body)
    (* TODO: check the type of a forall / see typical PTS ? *)
    | Forall | Exists -> ty body
  in
  let v_ty = v.Expr.id_type in
  if is_reduced v_ty && is_reduced body then begin
    mk_reduced ty t
  end else begin
    let v' = var_typed v (reduce v_ty) in
    let map = S.Id.bind S.empty v (id v') in
    (** the type of v' is reduced, && the body is reduced, therefore,
        the computed type of the bind in th erecursive call should take the
        first branch of the conditional and build a normal form. *)
    let reduced = lazy (bind b v' (subst map (reduce body))) in
    mk_normal ty t reduced
  end

and subst_aux s t =
  match t.term with
  | Type -> t
  | Id v ->
    begin
      try S.Id.get v s
      with Not_found -> t
    end
  | App (f, arg) ->
    let f' = subst_aux s f in
    let arg' = subst_aux s arg in
    if f == f' && arg == arg' then t else app f' arg'
  | Let (v, e, body) ->
    let e' = subst_aux s e in
    let s' = S.Id.remove v s in
    let v', s'' =
      if e.ty == e'.ty then v, s'
      else
        let v' = var_typed v e'.ty in
        v', S.Id.bind s' v (id v')
    in
    let body' = subst_aux s'' body in
    if v == v' && e == e' && body == body' then t else letin v' e' body'
  | Binder (b, v, body) ->
    let ty = v.Expr.id_type in
    let ty' = subst_aux s ty in
    let s' = S.Id.remove v s in
    let v', s'' =
      if ty == ty' then v, s'
      else
        let v' = var_typed v ty' in
        v', S.Id.bind s' v (id v')
    in
    let body' = subst_aux s'' body in
    if v == v' && body == body' then t else bind b v' body'

and subst s t =
  if S.is_empty s then t else subst_aux s t

and reduce_beta v e body =
  let body = reduce body in
  if not_occurs v body then body
  else begin
    let map = S.Id.bind S.empty v (reduce e) in
    (*
    reduce_chain map body
    *)
    let tmp = subst map body in
    reduce tmp
  end

(* Not really useful to speed up proof generation.
and reduce_chain map t =
  match t.term with
  | Let (v, e, body)
  | App ( { term = Binder (Lambda, v, body) ; _ } , e ) ->
    if not_occurs v body then
      reduce_chain map body
    else begin
      let map' = S.Id.bind map v (reduce e) in
      reduce_chain map' body
    end
  | _ ->
    let tmp = subst map t in
    reduce tmp
*)

(*
and reduce_binders map t =
  match t.term with
  | Binder (b, v, body) ->
    let ty = v.Expr.id_type in
    let ty' = subst map @@ reduce ty in
    let v' = if ty == ty' then v else var v.Expr.id_name ty' in
    let map' = if v == v' then map else S.Id.bind map v (id v') in
    let body' = reduce_binders map' body in
    if v == v' && body == body' then t else bind b v' body'
  | _ -> subst map @@ reduce t

and reduce_aux t =
  match t.term with
  | Type -> t
  | Id { Expr.builtin = Defined b; _ } -> b
  | Id _ -> t
  | Binder _ -> reduce_binders S.empty t
  | Let _ -> reduce_beta S.empty t
  | App (f, arg) ->
    let f' = reduce f in
    let arg' = reduce arg in
    let t' = if f == f' && arg == arg' then t else app f' arg' in
    reduce_beta S.empty t'
*)

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

(* Implicit arguments for printing *)
(* ************************************************************************ *)

let mk_flag () =
  let tag = Tag.create () in
  (fun v -> Expr.Id.tag v tag ()),
  (fun v ->
     match Expr.Id.get_tag v tag with
     | None -> false
     | Some () -> true
  )

let dot_implicit, is_dot_implicit = mk_flag ()
let coq_implicit, is_coq_implicit = mk_flag ()
let coq_inferred, is_coq_inferred = mk_flag ()
let tptp_implicit, is_tptp_implicit = mk_flag ()

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
  (* Format.eprintf "@\ninitializing imply_id@."; *)
  let a = var "A" _Prop in
  let b = var "B" _Prop in
  let t = lambda a (lambda b (arrow (id a) (id b))) in
  define "imply" t

let imply_term = id imply_id

let not_id =
  (* Format.eprintf "@\ninitializing not_id@."; *)
  let a = var "A" _Prop in
  let t = lambda a (apply imply_term [id a; false_term]) in
  define "not" t

let not_term = id not_id

let equal_id =
  (* Format.eprintf "@\ninitializing equal_id@."; *)
  let a_id = var "a" _Type in
  let () = coq_implicit a_id in
  let () = tptp_implicit a_id in
  let () = dot_implicit a_id in
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

let is_type_var v _ = equal _Type v.Expr.id_type
let not_type_var v _ = not (is_type_var v ())

let flatten_binder_aux cond b t =
  let rec aux b acc = function
    | { term = Binder (b', v, body) } when (b = b') && (cond v body) ->
      aux b (v :: acc) body
    | t ->
      if acc =  [] then begin
        Util.error "wrong flatten in: %a" pp t;
        assert false
      end else
        List.rev acc, t
  in
  aux b [] t

let flatten_binder t =
  let f, b, res =
    match t.term with
    | Binder (Forall, v, body) ->
      if is_type_var v () then is_type_var, Forall, `Pi
      else if occurs v body then occurs, Forall, `Binder Forall
      else if equal _Type t.ty then not_occurs, Forall, `Arrow
      else if equal _Prop t.ty then not_occurs, Forall, `Arrow
      else not_type_var, Forall, `Binder Forall
    | Binder (b, _, _) -> (fun _ _ -> true), b, `Binder b
    | _ -> assert false
  in
  let l, body = flatten_binder_aux f b t in
  res, l, body

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

(* Simplifing expressions before printing *)
(* ************************************************************************ *)

let contract t =
  try id @@ Hs.find definitions t
  with Not_found ->
    begin match t.term with
      | Binder (Forall, v, body) when equal body false_term ->
        app not_term v.Expr.id_type
      | _ -> t
    end

(* Printing *)
(* ************************************************************************ *)

let print_type fmt () =
  Format.fprintf fmt "Type"

let print_id fmt v =
  Expr.Id.print fmt v

let rec print_app fmt t =
  let f, args = uncurry_app t in
  if args = [] then begin
    Util.error ~section "wrong uncurry: %a" pp t;
    assert false
  end;
  Format.fprintf fmt "(%a@ %a)"
    print_aux f CCFormat.(list ~sep:(return "@ ") print_aux) args

and print_let fmt v e body =
  Format.fprintf fmt "@[<v>@[<hov>let %a =@ %a in@]@ %a@]"
    print_id v print_aux e print_aux body

and print_arrow fmt (l, body) =
  let l' = List.map (fun v -> v.Expr.id_type) l in
  let sep fmt () = Format.fprintf fmt " ->@ " in
  Format.fprintf fmt "(@[<hov>%a ->@ %a@])"
    CCFormat.(list ~sep print_aux) l' print_aux body

and print_var_list fmt (ty, l) =
  assert (l <> []);
  Format.fprintf fmt "(%a :@ %a)"
    CCFormat.(list ~sep:(return "@ ") print_id) l print_aux ty

and print_var_lists fmt l =
  CCFormat.(list ~sep:(return "@ ") print_var_list) fmt l

and print_binder fmt (b, l, body) =
  let l' = concat_vars l in
  Format.fprintf fmt "( @[<hov 2>%s @[<hov>%a@]%s@ %a@] )"
    (binder_name b) print_var_lists l'
    (binder_sep b) print_aux body

and print_aux fmt t =
  let t = contract t in
  match t.term with
  | Type -> print_type fmt ()
  | Id v -> print_id fmt v
  | App _ -> print_app fmt t
  | Let (v, e, body) -> print_let fmt v e body
  | Binder (b, _, _) ->
    let kind, l, body = flatten_binder t in
    begin match kind with
      | `Arrow -> print_arrow fmt (l, body)
      | `Pi | `Binder _ -> print_binder fmt (b, l, body)
    end

let print = CCFormat.hovbox print_aux

let print_typed fmt t =
  Format.fprintf fmt "@[<hv 2>%a :@ %a@]" print t print t.ty

(* Pattern matching *)
(* ************************************************************************ *)

let rec match_aux subst pat t =
  match pat, t with
  | { term = Id v }, _ when is_var v ->
    begin match S.Id.get v subst with
      | exception Not_found ->
        S.Id.bind (match_aux subst v.Expr.id_type t.ty) v t
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
    if b = b' then begin
      let tmp = match_aux subst v.Expr.id_type v'.Expr.id_type in
      match_aux (S.Id.bind tmp v (id v')) body body'
    end else
      raise (Match_Impossible (pat, t))
  | _ -> raise (Match_Impossible (pat, t))

let pmatch ~pat t =
  try match_aux S.empty pat t
  with Match_Impossible _ ->
    match_aux S.empty (reduce pat) (reduce t)

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
let of_id_aux ~kind tr ?callback id =
  (* Util.debug ~section "translate id: %a" Expr.Print.id id; *)
  match Expr.Id.get_tag id tr_tag with
  | Some v ->
    (* Util.debug ~section "cached value: %a" Expr.Print.id v; *)
    v
  | None ->
    let ty = tr ?callback id.Expr.id_type in
    let mk = match kind with
      | `Var -> var
      | `Declared | `Cst -> declare
    in
    let v = mk id.Expr.id_name ty in
    let () = Expr.Id.tag id tr_tag v in
    let () = if kind = `Cst then match callback with Some f -> f v | None -> () in
    (* Util.debug ~section "new cached id: %a" Expr.Print.id v; *)
    v

let of_id ~kind tr ?callback v = id (of_id_aux ~kind tr ?callback v)

let of_function_descr tr tr' ?callback fd =
  let rec aux_vars body = function
    | [] -> body
    | v :: r -> aux_vars (forall (of_id_aux ~kind:`Var ?callback tr v) body) r
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
  | { Expr.ty = Expr.TyVar v } -> of_id ~kind:`Var ?callback of_ttype v
  | { Expr.ty = Expr.TyMeta m } -> of_ty Synth.ty
  | { Expr.ty = Expr.TyApp (f, l) } ->
    let f' = of_id ~kind:`Cst ?callback (of_function_descr of_unit of_ttype) f in
    let l' = List.map of_ty l in
    apply f' l'

and of_ty ?callback ty =
  (* Util.debug ~section "translate ty: %a" Expr.Print.ty ty; *)
  match Hty.find ty_cache ty with
  | res ->
    (* Util.debug ~section "cached value: %a" print res; *)
    res
  | exception Not_found ->
    let res = of_ty_aux ?callback ty in
    let () = Hty.add ty_cache ty res in
    (* Util.debug ~section "new cached ty: %a" print res; *)
    res

(* Term translation *)
let rec of_term_aux ?callback = function
  | { Expr.term = Expr.Var v } ->
    of_id ~kind:`Var ?callback of_ty v
  | { Expr.term = Expr.Meta m } as t ->
    of_term ?callback (Synth.term Expr.(t.t_type))
  | { Expr.term = Expr.App (f, tys, args) } ->
    let f' = of_id ~kind:`Cst ?callback (of_function_descr of_ttype of_ty) f in
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
    foralls (List.map (of_id_aux ~kind:`Var ?callback of_ttype) tys) @@
    foralls (List.map (of_id_aux ~kind:`Var ?callback of_ty) ts) (of_formula ?callback body)
  | Expr.Ex ((tys, ts), _, body) ->
    exists (List.map (of_id_aux ~kind:`Var ?callback of_ttype) tys) @@
    exists (List.map (of_id_aux ~kind:`Var ?callback of_ty) ts) (of_formula ?callback body)

and of_tree ?callback t = function
  | Expr.F f -> of_formula ?callback f
  | Expr.L l -> apply_left t @@ List.map (of_tree ?callback t) l

(* Disambiguate terms *)
(* ************************************************************************ *)

let disambiguate_tag = Tag.create ()

module M = Map.Make(String)

type env = {
  names : id M.t;
}

let empty_env = { names = M.empty; }

let full_name v = v.Expr.id_name

let disambiguation_collision env v name =
  Util.error ~section
    "@[<hov>While@ disambiguating,@ encountered@ already@ disambiguated@ variable@ '%a',@ with@ name@ '%s',@ which@ is@ already@ taken by@ %a"
    Expr.Id.print v name Expr.Id.print (M.find name env.names);
  raise (Invalid_argument "Term.bind_ambiguous")

let add_name reason env v name =
  assert (not (M.mem name env.names));
  Util.debug ~section "(%s) %a ~~~> %s" reason Expr.Id.print v name;
  { (* env with *) names = M.add name v env.names }

let find_unambiguous env v =
  let new_name = Format.asprintf "%s#%d" v.Expr.id_name (v.Expr.index :> int) in
  if M.mem new_name env.names
  then disambiguation_collision env v new_name
  else begin
    Util.debug ~section "(renaming) %a ###> %s" Expr.Id.print v new_name;
    Expr.Id.tag v disambiguate_tag (Pretty.Renamed new_name);
    new_name
  end

let bind_ambiguous env v =
  match Expr.Id.get_tag v disambiguate_tag with
  | None ->
    let name = full_name v in
    if not @@ M.mem name env.names then
      add_name "std:binding" env v name
    else
      add_name "disambiguated" env v (find_unambiguous env v)
  | Some Pretty.Exact s -> assert false
  | Some Pretty.Renamed s ->
    if M.mem s env.names
    then disambiguation_collision env v s
    else add_name "renamed" env v s

let rec disambiguate_aux env t =
  match t.term with
  | Type | Id _ -> ()
  | App (f, arg) ->
    disambiguate_aux env f;
    disambiguate_aux env arg
  | Let (v, e, body) ->
    disambiguate_aux env e;
    let env' = bind_ambiguous env v in
    disambiguate_aux env' body
  | Binder (b, v, body) ->
    let env' = bind_ambiguous env v in
    disambiguate_aux env' body

let disambiguate t =
  Util.debug ~section "@[<hv 2>disambiguate:@ @[<hov>%a@]@]" print t;
  disambiguate_aux empty_env t


