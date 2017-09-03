
(* Log&Module Init *)
(* ************************************************************************ *)

let section = Section.make "type"

let stack = Backtrack.Stack.create (
    Section.make ~parent:section "backtrack")

module Ast = Dolmen.Term
module Id = Dolmen.Id

let get_loc =
  let default_loc = Dolmen.ParseLocation.mk "<?>" 0 0 0 0 in
  (fun t -> CCOpt.get_or ~default:default_loc t.Ast.loc)

module E = Map.Make(struct
    type t = Expr.ttype Expr.id
    let compare = Expr.Id.compare
  end)
module F = Map.Make(struct
    type t = Expr.ty Expr.id
    let compare = Expr.Id.compare
  end)

module R = Backtrack.Hashtbl(struct
    type t = Expr.ttype Expr.function_descr Expr.id
    let hash = Expr.Id.hash
    let equal = Expr.Id.equal
  end)
module S = Backtrack.Hashtbl(struct
    type t = Expr.ty Expr.function_descr Expr.id
    let hash = Expr.Id.hash
    let equal = Expr.Id.equal
  end)

(* Fuzzy search maps *)
(* ************************************************************************ *)

module M = struct

  module S = Spelll
  module I = S.Index

  (** We use fuzzy maps in order to give suggestions in case of typos.
      Since such maps are not trivial to extend to Dolmen identifiers,
      we map strings (identifier names) to list of associations. *)
  type 'a t = (Id.t * 'a) list I.t

  let eq = Id.equal

  let empty = I.empty

  let get t id =
    let s = Id.(id.name) in
    match S.klist_to_list (I.retrieve ~limit:0 t s) with
    | [l] -> l
    | [] -> []
    | _ -> assert false

  let mem id t =
    CCList.Assoc.mem ~eq id (get t id)

  let find id t =
    CCList.Assoc.get_exn ~eq id (get t id)

  let add id v t =
    let l = get t id in
    let l' = CCList.Assoc.set ~eq id v l in
    I.add t Dolmen.Id.(id.name) l'

  let iter f t =
    I.iter (fun _ l -> List.iter (fun (id, v) -> f id v) l) t

  (** Return a list of suggestions for an identifier. *)
  let suggest ~limit id t =
    let s = Id.(id.name) in
    let l = S.klist_to_list (I.retrieve ~limit t s) in
    CCList.flat_map (List.map fst) l

end

(* Fuzzy search hashtables *)
(* ************************************************************************ *)

module H = struct

  (** Fuzzy hashtables are just references to fuzzy maps.
      The reference is registered on the stack to allow backtracking. *)
  let create stack =
    let r = ref M.empty in
    Backtrack.Stack.attach stack r;
    r

  let mem r id = M.mem id !r

  let find r id = M.find id !r

  let suggest r id = M.suggest id !r

  let add r id v =
    r := M.add id v !r

end

(* Types *)
(* ************************************************************************ *)

(* The type of reasons for constant typing *)
type reason =
  | Inferred of Dolmen.ParseLocation.t
  | Declared of Dolmen.ParseLocation.t

(* The type of potentially expected result type for parsing an expression *)
type expect =
  | Nothing
  | Type
  | Typed of Expr.ty

(* The type returned after parsing an expression. *)
type tag = Any : 'a Tag.t * 'a -> tag

type res =
  | Ttype   : res
  | Ty      : Expr.ty -> res
  | Term    : Expr.term -> res
  | Formula : Expr.formula -> res
  | Tags    : tag list -> res

type inferred =
  | Ty_fun of Expr.ttype Expr.function_descr Expr.id
  | Term_fun of Expr.ty Expr.function_descr Expr.id

(* The local environments used for type-checking. *)
type env = {

  (* Map from term variables to the reason of its type *)
  type_locs : reason E.t;
  term_locs : reason F.t;

  (* local variables (mostly quantified variables) *)
  type_vars : (Expr.ttype Expr.id)  M.t;
  term_vars : (Expr.ty Expr.id)     M.t;

  (* Bound variables (through let constructions) *)
  term_lets : Expr.term     M.t;
  prop_lets : Expr.formula  M.t;

  (* The current builtin symbols *)
  builtins : builtin_symbols;

  (* Additional typing info *)
  expect      : expect;
  infer_hook  : env -> inferred -> unit;
  status      : Expr.status;
  explain     : [ `No | `Yes | `Full ];
}

(* Builtin symbols, i.e symbols understood by some theories,
   but which do not have specific syntax, so end up as special
   cases of application. *)
and builtin_symbols = env -> Dolmen.Term.t -> Dolmen.Id.t -> Ast.t list -> res option

type 'a typer = env -> Dolmen.Term.t -> 'a


(* Global Environment *)
(* ************************************************************************ *)

(* Global identifier table; stores declared types and aliases.
   Ttype location table: stores reasons for typing of type constructors
   Const location table : stores reasons for typing of constants *)
let global_env = H.create stack
let ttype_locs = R.create stack
let const_locs = S.create stack

let find_global name =
  try H.find global_env name
  with Not_found -> `Not_found

(* Symbol declarations *)
let decl_ty_cstr id c reason =
  if H.mem global_env id then
    Util.warn ~section
      "Symbol '%a' has already been defined, overwriting previous definition"
      Id.print id;
  H.add global_env id (`Ty c);
  R.add ttype_locs c reason;
  Util.info ~section
    "New type constructor : @[<hov>%a@]" Expr.Print.const_ttype c

let decl_term id c reason =
  if H.mem global_env id then
    Util.warn ~section
      "Symbol '%a' has already been defined, overwriting previous definition"
      Id.print id;
  H.add global_env id (`Term c);
  S.add const_locs c reason;
  Util.info ~section "New constant : @[<hov>%a@]" Expr.Print.const_ty c

(* Symbol definitions *)
let def_ty id args body =
  if H.mem global_env id then
    Util.warn ~section
      "Symbol '%a' has already been defined, overwriting previous definition"
      Id.print id;
  H.add global_env id (`Ty_alias (args, body));
  Util.info ~section "@[<hov 4>New type alias:@ @[<hov>%a(%a)@] =@ %a@]"
    Id.print id
        (CCFormat.list Expr.Print.id_ttype) args
        Expr.Print.ty body

let def_term id ty_args args body =
  if H.mem global_env id then
    Util.warn ~section
      "Symbol '%a' has already been defined, overwriting previous definition"
      Id.print id;
  H.add global_env id (`Term_alias (ty_args, args, body));
  Util.info ~section "@[<hov 4>New term alias:@ @[<hov>%a(%a;%a)@] =@ %a@]"
    Id.print id
        (CCFormat.list Expr.Print.id_ttype) ty_args
        (CCFormat.list Expr.Print.id_ty) args
        Expr.Print.term body

(* Local Environment *)
(* ************************************************************************ *)

(* Make a new empty environment *)
let empty_env
    ?(expect=Nothing)
    ?(status=Expr.Status.hypothesis)
    ?(infer_hook=(fun _ _ -> ()))
    ?(explain=`No)
    builtins = {
  type_locs = E.empty;
  term_locs = F.empty;
  type_vars = M.empty;
  term_vars = M.empty;
  term_lets = M.empty;
  prop_lets = M.empty;
  builtins; expect; infer_hook; status; explain;
}

let expect ?(force=false) env expect =
  if env.expect = Nothing && not force then env
  else { env with expect = expect }

(* Generate new fresh names for shadowed variables *)
let new_name pre =
  let i = ref 0 in
  (fun () -> incr i; pre ^ (string_of_int !i))

let new_ty_name = new_name "ty#"
let new_term_name = new_name "term#"

(* Add local variables to environment *)
let add_type_var env id v loc =
  let v' =
    if M.mem id env.type_vars then
      Expr.Id.ttype (new_ty_name ())
    else
      v
  in
  Util.info ~section "New binding: @[<hov>%a ->@ %a@]"
    Id.print id Expr.Print.id_ttype v';
  v', { env with
        type_vars = M.add id v' env.type_vars;
        type_locs = E.add v' (Declared loc) env.type_locs;
      }

let add_type_vars env l =
  let l', env' = List.fold_left (fun (l, acc) (id, v, loc) ->
      let v', acc' = add_type_var acc id v loc in
      v' :: l, acc') ([], env) l in
  List.rev l', env'

let add_term_var env id v loc =
  let v' =
    if M.mem id env.type_vars then
      Expr.Id.ty (new_term_name ()) Expr.(v.id_type)
    else
      v
  in
  Util.info ~section "New binding: @[<hov>%a ->@ %a@]"
    Id.print id Expr.Print.id_ty v';
  v', { env with
        term_vars = M.add id v' env.term_vars;
        term_locs = F.add v' (Declared loc) env.term_locs;
      }

let find_var env name =
  try `Ty (M.find name env.type_vars)
  with Not_found ->
    begin
      try
        `Term (M.find name env.term_vars)
      with Not_found ->
        `Not_found
    end

(* Add local bound variables to env *)
let add_let_term env id t =
  Util.info ~section "New let-binding: @[<hov>%a ->@ %a@]" Id.print id Expr.Print.term t;
  { env with term_lets = M.add id t env.term_lets }

let add_let_prop env id t =
  Util.info ~section "New let-binding: @[<hov>%a ->@ %a@]" Id.print id Expr.Print.formula t;
  { env with prop_lets = M.add id t env.prop_lets }

let find_let env name =
  try `Term (M.find name env.term_lets)
  with Not_found ->
    begin
      try
        `Prop (M.find name env.prop_lets)
      with Not_found ->
        `Not_found
    end

(* Printing *)
let print_expect fmt = function
  | Nothing   -> Format.fprintf fmt "<>"
  | Type      -> Format.fprintf fmt "<tType>"
  | Typed ty  -> Expr.Print.ty fmt ty

let print_map print fmt map =
  let aux k v =
    Format.fprintf fmt "%a ->@ @[<hov>%a@];@ " Id.print k print v
  in
  M.iter aux map

let pp_env fmt env =
  Format.fprintf fmt "@[<hov 2>(%a) %a%a%a%a@]"
    print_expect env.expect
    (print_map Expr.Print.id_ttype) env.type_vars
    (print_map Expr.Print.id_ty) env.term_vars
    (print_map Expr.Print.term) env.term_lets
    (print_map Expr.Print.formula) env.prop_lets

(* Typo suggestion *)
(* ************************************************************************ *)

let suggest ~limit env fmt id =
  let l =
    M.suggest ~limit id env.type_vars @
    M.suggest ~limit id env.term_vars @
    M.suggest ~limit id env.term_lets @
    M.suggest ~limit id env.prop_lets @
    H.suggest ~limit global_env id
  in
  if l = [] then
    Format.fprintf fmt "coming up empty, sorry, ^^"
  else
    CCFormat.list Id.print fmt l

(* Typing explanation *)
(* ************************************************************************ *)

exception Continue of Expr.term list

let get_reason_loc = function Inferred l | Declared l -> l

let pp_reason fmt = function
  | Inferred loc -> Format.fprintf fmt "inferred at %a" Dolmen.ParseLocation.fmt loc
  | Declared loc -> Format.fprintf fmt "declared at %a" Dolmen.ParseLocation.fmt loc

let rec explain ~full env fmt t =
  try
    begin match t with
      | { Expr.term = Expr.Var v } ->
        let reason = F.find v env.term_locs in
        Format.fprintf fmt "%a was %a\n" Expr.Print.id_ty v pp_reason reason
      | { Expr.term = Expr.Meta m } ->
        let f = Expr.Meta.ty_def Expr.(m.meta_index) in
        Format.fprintf fmt "%a was defined by %a\n"
          Expr.Print.meta m Expr.Print.formula f
      | { Expr.term = Expr.App (f, _, l) } ->
        let reason = S.find const_locs f in
        Format.fprintf fmt "%a was %a\n" Expr.Print.const_ty f pp_reason reason;
        if full then raise (Continue l)
    end with
  | Not_found ->
    Format.fprintf fmt "Couldn't find a reason..."
  | Continue l ->
    List.iter (explain env ~full fmt) l

(* Exceptions *)
(* ************************************************************************ *)

(* Internal exception *)
exception Found of Ast.t * res

(* Exception for typing errors *)
exception Typing_error of string * env * Ast.t

(* Creating explanations *)
let mk_expl preface env fmt t =
  match env.explain with
  | `No -> ()
  | `Yes ->
    Format.fprintf fmt "%s\n%a" preface (explain ~full:false env) t
  | `Full ->
    Format.fprintf fmt "%s\n%a" preface (explain ~full:true env) t

(* Convenience functions *)
let _expected env s t res =
  let msg = match res with
    | None -> "the expression doesn't match what was expected"
    | Some r ->
      let tmp =
        match r with
        | Ttype -> "the Ttype constant"
        | Ty _ -> "a type"
        | Term _ -> "a first-order term"
        | Formula _ -> "a first-order formula"
        | Tags _ -> "a tag/attribute list"
      in
      Format.sprintf "got %s" tmp
  in
  let msg = Format.asprintf "Expected a %s, but %s" s msg in
  raise (Typing_error (msg, env, t))

let _bad_op_arity env s n t =
  let msg = Format.asprintf "Bad arity for operator '%s' (expected %d arguments)" s n in
  raise (Typing_error (msg, env, t))

let _bad_id_arity env id n t =
  let msg = Format.asprintf
      "Bad arity for identifier '%a' (expected %d arguments)" Id.print id n
  in
  raise (Typing_error (msg, env, t))

let _bad_term_arity env f n t =
  let msg = Format.asprintf
      "Bad arity for function '%a' (expected %d arguments)" Expr.Print.id f n
  in
  raise (Typing_error (msg, env, t))

let _fo_let env s t =
  let msg = Format.asprintf "Let-bound variable '%a' is applied to terms" Id.print s in
  raise (Typing_error (msg, env, t))

let _fo_formula env f ast =
  let msg = Format.asprintf "Cannot apply formula '%a' to arguments" Expr.Print.formula f in
  raise (Typing_error (msg, env, ast))

let _type_mismatch env t ty ty' ast =
  let msg = Format.asprintf
      "Type Mismatch: an expression of type %a was expected, but '%a' has type %a%a"
      Expr.Print.ty ty' Expr.Print.term t Expr.Print.ty ty (mk_expl ", because:" env) t
  in
  raise (Typing_error (msg, env, ast))

let _cannot_unify env ast ty t =
  let msg = Format.asprintf
      "A term of type '%a'@ was expected, but could not unify it with@ %a:@ %a"
      Expr.Print.ty ty Expr.Print.term t Expr.Print.ty Expr.(t.t_type)
  in
  raise (Typing_error (msg, env, ast))

let _cannot_infer_quant_var env t =
  raise (Typing_error ("Cannot infer the type of a quantified variable", env, t))

(* Wrappers for expression building *)
(* ************************************************************************ *)

(* Generate metas for wildcards in types. *)
let gen_wildcard =
  let i = ref ~-1 in
  (function () -> (* TODO: add location information? *)
     incr i; Expr.Id.ttype (Format.sprintf "?%d" !i))

let wildcard =
  (fun env ast id l ->
     match l with
     | [] ->
       let v = gen_wildcard () in
       Ty (Expr.Ty.of_id v)
     | _ -> _bad_id_arity env id 0 ast
  )

let arity f =
  List.length Expr.(f.id_type.fun_vars) +
  List.length Expr.(f.id_type.fun_args)

(* Wrapper around type application *)
let ty_apply env ast f args =
  try
    Expr.Ty.apply ~status:env.status f args
  with Expr.Bad_ty_arity _ ->
    _bad_term_arity env f (arity f) ast

(* Wrapper aroun term application. Since wildcards are allowed in types,
   there may be some variables in [ty_args], so we have to find an appropriate
   substitution for these variables. To do that, we try and unify the expected type
   and the actual argument types. *)
let term_apply env ast f ty_args t_args =
  if List.length Expr.(f.id_type.fun_vars) <> List.length ty_args ||
     List.length Expr.(f.id_type.fun_args) <> List.length t_args then
    _bad_term_arity env f (arity f) ast
  else
    let map =
      List.fold_left2
        Mapping.Var.bind_ty Mapping.empty
        Expr.(f.id_type.fun_vars) ty_args
    in
    let expected_types =
      List.map (Mapping.apply_ty map) Expr.(f.id_type.fun_args)
    in
    let subst =
      List.fold_left2 (fun subst expected term ->
          try
            Unif.Robinson.ty subst expected Expr.(term.t_type)
          with
          | Unif.Robinson.Impossible_ty _ ->
            _cannot_unify env ast expected term
        ) map expected_types t_args
    in
    let actual_ty_args = List.map (Mapping.apply_ty subst) ty_args in
    try
      Expr.Term.apply ~status:env.status f actual_ty_args t_args
    with
    | Expr.Bad_arity _ | Expr.Type_mismatch _ ->
      Util.debug ~section "%a, typing:@\n %a :: %a :: %a@\nsubst: %a"
        Dolmen.ParseLocation.fmt (get_loc ast) Expr.Print.const_ty f
        (CCFormat.list Expr.Print.ty) ty_args
        (CCFormat.list Expr.Print.term) t_args
        Mapping.print subst;
      assert false

let ty_subst env ast_term id args f_args body =
  match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_args args with
  | subst ->
    Expr.Ty.subst subst Expr.Subst.empty body
  | exception Invalid_argument _ ->
    _bad_id_arity env id (List.length f_args) ast_term

let term_subst env ast_term id ty_args t_args f_ty_args f_t_args body =
  match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_ty_args ty_args with
  | ty_subst ->
    begin
      match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_t_args t_args with
      | t_subst ->
        Expr.Term.subst ty_subst Expr.Subst.empty t_subst Expr.Subst.empty body
      | exception Invalid_argument _ ->
        _bad_id_arity env id (List.length f_ty_args + List.length f_t_args) ast_term
    end
  | exception Invalid_argument _ ->
    _bad_id_arity env id (List.length f_ty_args + List.length f_t_args) ast_term

let make_eq env ast_term a b =
  try
    Expr.Formula.eq a b
  with Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch env t ty ty' ast_term

let make_pred env ast_term p =
  try
    Expr.Formula.pred p
  with Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch env t ty ty' ast_term

let mk_quant_ty env mk vars body =
  (* Check that all quantified variables are actually used *)
  let fv_ty, fv_t = Expr.Formula.fv body in
  let unused = List.filter (fun v -> not @@ CCList.mem ~eq:Expr.Id.equal v fv_ty) vars in
  List.iter (fun v ->
      Util.warn "%a:@\nQuantified variables unused: %a"
        Dolmen.ParseLocation.fmt (get_reason_loc (E.find v env.type_locs))
        Expr.Print.id v) unused;
  mk vars body

let mk_quant_term env mk vars body =
  (* Check that all quantified variables are actually used *)
  let fv_ty, fv_t = Expr.Formula.fv body in
  let unused = List.filter (fun v -> not @@ CCList.mem ~eq:Expr.Id.equal v fv_t) vars in
  List.iter (fun v ->
      Util.warn "%a:@\nQuantified variables unused: %a"
        Dolmen.ParseLocation.fmt (get_reason_loc (F.find v env.term_locs))
        Expr.Print.id v) unused;
  mk vars body

let promote env ast t =
  match t with
  | Term t when Expr.(Ty.equal Ty.prop t.t_type) ->
    Formula (make_pred env ast t)
  | _ -> t

let infer env s args loc =
  match env.expect with
  | Nothing -> None
  | Type ->
    let n = List.length args in
    let ret = Expr.Id.ty_fun (Id.full_name s) n in
    let res = Ty_fun ret in
    env.infer_hook env res;
    decl_ty_cstr s ret (Inferred loc);
    Some res
  | Typed ty ->
    let n = List.length args in
    let ret = Expr.Id.term_fun (Id.full_name s) [] (CCList.replicate n Expr.Ty.base) ty in
    let res = Term_fun ret in
    env.infer_hook env res;
    decl_term s ret (Inferred loc);
    Some res


(* Tag application *)
(* ************************************************************************ *)

let apply_tag env ast tag v = function
  | Ttype -> raise (Typing_error ("Cannot tag Ttype", env, ast))
  | Tags _ -> raise (Typing_error ("Cannot tag a tag list", env, ast))
  | Ty ty -> Expr.Ty.tag ty tag v
  | Term t -> Expr.Term.tag t tag v
  | Formula f -> Expr.Formula.tag f tag v

(* Expression parsing *)
(* ************************************************************************ *)

let rec parse_expr (env : env) t =
  Util.debug ~section
    "parsing: @[<hov>%a@]@\nin env: @[<hov>%a@]"
    Ast.print t pp_env env;
  let res = match t with

    (* Ttype & builtin types *)
    | { Ast.term = Ast.Builtin Ast.Ttype } ->
      Ttype
    | { Ast.term = Ast.Builtin Ast.Prop } ->
      Ty Expr.Ty.prop

    (* Wildcards (only allowed in types *)
    | { Ast.term = Ast.Builtin Ast.Wildcard } ->
      Ty (Expr.Ty.of_id (gen_wildcard ()))

    (* Basic formulas *)
    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.True }, []) }
    | { Ast.term = Ast.Builtin Ast.True } ->
      Formula Expr.Formula.f_true

    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.False }, []) }
    | { Ast.term = Ast.Builtin Ast.False } ->
      Formula Expr.Formula.f_false

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.And}, l) } ->
      Formula (Expr.Formula.f_and (List.map (parse_formula env) l))

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Or}, l) } ->
      Formula (Expr.Formula.f_or (List.map (parse_formula env) l))

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Xor}, l) } as t ->
      begin match l with
        | [p; q] ->
          let f = parse_formula env p in
          let g = parse_formula env q in
          Formula (Expr.Formula.neg (Expr.Formula.equiv f g))
        | _ -> _bad_op_arity env "xor" 2 t
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Imply}, l) } as t ->
      begin match l with
        | [p; q] ->
          let f = parse_formula env p in
          let g = parse_formula env q in
          Formula (Expr.Formula.imply f g)
        | _ -> _bad_op_arity env "=>" 2 t
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv}, l) } as t ->
      begin match l with
        | [p; q] ->
          let f = parse_formula env p in
          let g = parse_formula env q in
          Formula (Expr.Formula.equiv f g)
        | _ -> _bad_op_arity env "<=>" 2 t
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Not}, l) } as t ->
      begin match l with
        | [p] ->
          Formula (Expr.Formula.neg (parse_formula env p))
        | _ -> _bad_op_arity env "not" 1 t
      end

    (* Binders *)
    | { Ast.term = Ast.Binder (Ast.All, vars, f) } ->
      let ttype_vars, ty_vars, env' =
        parse_quant_vars (expect env (Typed Expr.Ty.base)) vars in
      Formula (
        mk_quant_ty env' Expr.Formula.allty ttype_vars
          (mk_quant_term env' Expr.Formula.all ty_vars
             (parse_formula env' f)))

    | { Ast.term = Ast.Binder (Ast.Ex, vars, f) } ->
      let ttype_vars, ty_vars, env' =
        parse_quant_vars (expect env (Typed Expr.Ty.base)) vars in
      Formula (
        mk_quant_ty env' Expr.Formula.exty ttype_vars
          (mk_quant_term env' Expr.Formula.ex ty_vars
             (parse_formula env' f)))

    (* (Dis)Equality *)
    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Eq}, l) } as t ->
      begin match l with
        | [a; b] ->
          begin match promote env t @@ parse_expr env a,
                      promote env t @@ parse_expr env b with
            | Term t1, Term t2 ->
              Formula (make_eq env t t1 t2)
            | Formula f1, Formula f2 ->
              Formula (Expr.Formula.equiv f1 f2)
            | _ ->
              _expected env "either two terms or two formulas" t None
          end
        | _ -> _bad_op_arity env "=" 2 t
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Distinct}, args) } as t ->
      let l' = List.map (parse_term env) args in
      let l'' = CCList.diagonal l' in
      let l''' = List.map (fun (a, b) -> Expr.Formula.neg (make_eq env t a b)) l'' in
      let f = match l''' with
        | [f] -> f
        | _ -> Expr.Formula.f_and l'''
      in
      Formula f

    (* General case: application *)
    | { Ast.term = Ast.Symbol s } as ast ->
      parse_app env ast s []
    | { Ast.term = Ast.App ({ Ast.term = Ast.Symbol s }, l) } as ast ->
      parse_app env ast s l

    (* Local bindings *)
    | { Ast.term = Ast.Binder (Ast.Let, vars, f) } ->
      parse_let env f vars

    (* Other cases *)
    | ast -> raise (Typing_error ("Unexpected construction", env, ast))
  in
  apply_attr env res t t.Ast.attr

and apply_attr env res ast l =
  let () = List.iter (function
      | Any (tag, v) ->
        apply_tag env ast tag v res;
    ) (parse_attrs env ast [] l) in
  res

and parse_attr_and env ast =
  match ast with
  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.And}, l) } ->
    parse_attrs env ast [] l
  | _ -> parse_attrs env ast [] [ast]

and parse_attrs env ast acc = function
  | [] -> acc
  | a :: r ->
    begin match parse_expr (expect env Nothing) a with
      | Tags l ->
        parse_attrs env ast (l @ acc) r
      | res ->
        _expected env "tag" a (Some res)
      | exception (Typing_error (msg, _, t)) ->
        Util.warn ~section "%a while parsing an attribute:@\n%s"
          Dolmen.ParseLocation.fmt (get_loc t) msg;
        parse_attrs env ast acc r
    end

and parse_var env = function
  | { Ast.term = Ast.Colon ({ Ast.term = Ast.Symbol s }, e) } ->
    begin match parse_expr env e with
      | Ttype -> `Ty (s, Expr.Id.ttype (Id.full_name s))
      | Ty ty -> `Term (s, Expr.Id.ty (Id.full_name s) ty)
      | res -> _expected env "type (or Ttype)" e (Some res)
    end
  | { Ast.term = Ast.Symbol s } as t ->
    begin match env.expect with
      | Nothing -> _cannot_infer_quant_var env t
      | Type -> `Ty (s, Expr.Id.ttype (Id.full_name s))
      | Typed ty -> `Term (s, Expr.Id.ty (Id.full_name s) ty)
    end
  | t -> _expected env "(typed) variable" t None

and parse_quant_vars env l =
  let ttype_vars, typed_vars, env' = List.fold_left (
      fun (l1, l2, acc) v ->
        match parse_var acc v with
        | `Ty (id, v') ->
          let v'', acc' = add_type_var acc id v' (get_loc v) in
          (v'' :: l1, l2, acc')
        | `Term (id, v') ->
          let v'', acc' = add_term_var acc id v' (get_loc v) in
          (l1, v'' :: l2, acc')
    ) ([], [], env) l in
  List.rev ttype_vars, List.rev typed_vars, env'

and parse_let env f = function
  | [] -> parse_expr env f
  | x :: r ->
    begin match x with
      | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Eq}, [
          { Ast.term = Ast.Symbol s }; e]) } ->
        let t = parse_term env e in
        let env' = add_let_term env s t in
        parse_let env' f r
      | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv}, [
          { Ast.term = Ast.Symbol s }; e]) } ->
        let t = parse_formula env e in
        let env' = add_let_prop env s t in
        parse_let env' f r
      | { Ast.term = Ast.Colon ({ Ast.term = Ast.Symbol s }, e) } ->
        begin match parse_expr env e with
          | Term t ->
            let env' = add_let_term env s t in
            parse_let env' f r
          | Formula t ->
            let env' = add_let_prop env s t in
            parse_let env' f r
          | res -> _expected env "term or formula" e (Some res)
        end
      | t -> _expected env "let-binding" t None
    end

and parse_app env ast s args =
  match find_let env s with
  | `Term t ->
    if args = [] then Term t
    else _fo_let env s ast
  | `Prop p ->
    if args = [] then Formula p
    else _fo_let env s ast
  | `Not_found ->
    begin match find_var env s with
      | `Ty f ->
        if args = [] then Ty (Expr.Ty.of_id f)
        else _fo_let env s ast
      | `Term f ->
        if args = [] then Term (Expr.Term.of_id f)
        else _fo_let env s ast
      | `Not_found ->
        begin match find_global s with
          | `Ty f ->
            parse_app_ty env ast f args
          | `Term f ->
            parse_app_term env ast f args
          | `Ty_alias (f_args, body) ->
            parse_app_subst_ty env ast s args f_args body
          | `Term_alias (f_ty_args, f_t_args, body) ->
            parse_app_subst_term env ast s args f_ty_args f_t_args body
          | `Not_found ->
            begin match env.builtins env ast s args with
              | Some res -> res
              | None ->
                begin match infer env s args (get_loc ast) with
                  | Some Ty_fun f -> parse_app_ty env ast f args
                  | Some Term_fun f -> parse_app_term env ast f args
                  | None ->
                    Util.error ~section
                      "Looking up '%a' failed, possibilities were:@ @[<hov>%a@]"
                      Id.print s (suggest ~limit:1 env) s;
                    raise (Typing_error (
                        Format.asprintf "Scoping error: '%a' not found" Id.print s, env, ast))
                end
            end
        end
    end

and parse_app_ty env ast f args =
  let l = List.map (parse_ty env) args in
  Ty (ty_apply env ast f l)

and parse_app_term env ast f args =
  let n_args = List.length args in
  let n_ty = List.length Expr.(f.id_type.fun_vars) in
  let n_t = List.length Expr.(f.id_type.fun_args) in
  let ty_l, t_l =
    if n_args = n_ty + n_t then
      CCList.take_drop n_ty args
    else if n_args = n_t then
      (CCList.replicate n_ty Dolmen.Term.wildcard, args)
    else
      _bad_term_arity env f (n_ty + n_t) ast
  in
  let ty_args = List.map (parse_ty env) ty_l in
  let t_args = List.map (parse_term env) t_l in
  Term (term_apply env ast f ty_args t_args)

and parse_app_formula env ast f args =
  if args = [] then Formula f
  else _fo_formula env f ast

and parse_app_subst_ty env ast id args f_args body =
  let l = List.map (parse_ty env) args in
  Ty (ty_subst env ast id l f_args body)

and parse_app_subst_term env ast id args f_ty_args f_t_args body =
  let n = List.length f_ty_args in
  let ty_l, t_l = CCList.take_drop n args in
  let ty_args = List.map (parse_ty env) ty_l in
  let t_args = List.map (parse_term env) t_l in
  Term (term_subst env ast id ty_args t_args f_ty_args f_t_args body)

and parse_ty env ast =
  match parse_expr (expect env Type) ast with
  | Ty ty -> ty
  | res -> _expected env "type" ast (Some res)

and parse_term env ast =
  match parse_expr (expect env (Typed Expr.Ty.base)) ast with
  | Term t -> t
  | res -> _expected env "term" ast (Some res)

and parse_formula env ast =
  match promote env ast @@ parse_expr (expect env (Typed Expr.Ty.prop)) ast with
  | Formula p -> p
  | res -> _expected env "formula" ast (Some res)

let parse_ttype_var env t =
  match parse_var (expect ~force:true env Type) t with
  | `Ty (id, v) -> (id, v, get_loc t)
  | `Term (_, v) ->
    _expected env "type variable" t (Some (Term (Expr.Term.of_id v)))

let rec parse_sig_quant env = function
  | { Ast.term = Ast.Binder (Ast.Pi, vars, t) } ->
    let ttype_vars = List.map (parse_ttype_var env) vars in
    let ttype_vars', env' = add_type_vars env ttype_vars in
    let l = List.combine vars ttype_vars' in
    parse_sig_arrow l [] env' t
  | t ->
    parse_sig_arrow [] [] env t

and parse_sig_arrow ttype_vars (ty_args: (Ast.t * res) list) env = function
  | { Ast.term = Ast.Binder (Ast.Arrow, args, ret) } ->
    let t_args = parse_sig_args env args in
    parse_sig_arrow ttype_vars (ty_args @ t_args) env ret
  | t ->
    begin match parse_expr env t with
      | Ttype ->
        begin match ttype_vars with
          | (h, _) :: _ ->
            raise (Typing_error (
                "Type constructor signatures cannot have quantified type variables", env, h))
          | [] ->
            let aux n = function
              | (_, Ttype) -> n + 1
              | (ast, res) -> raise (Found (ast, res))
            in
            begin
              match List.fold_left aux 0 ty_args with
              | n -> `Ty_cstr n
              | exception Found (err, _) ->
                raise (Typing_error (
                    Format.asprintf
                      "Type constructor signatures cannot have non-ttype arguments,", env, err))
            end
        end
      | Ty ret ->
        let aux acc = function
          | (_, Ty t) -> t :: acc
          | (ast, res) -> raise (Found (ast, res))
        in
        begin
          match List.fold_left aux [] ty_args with
          | exception Found (err, res) -> _expected env "type" err (Some res)
          | l -> `Fun_ty (List.map snd ttype_vars, List.rev l, ret)
        end
      | res -> _expected env "Ttype of type" t (Some res)
    end

and parse_sig_args env l =
  CCList.flat_map (parse_sig_arg env) l

and parse_sig_arg env = function
  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Product}, l) } ->
    List.map (fun x -> x, parse_expr env x) l
  | t ->
    [t, parse_expr env t]

let parse_sig = parse_sig_quant

let rec parse_fun ty_args t_args env = function
  | { Ast.term = Ast.Binder (Ast.Fun, l, ret) } ->
    let ty_args', t_args', env' = parse_quant_vars env l in
    parse_fun (ty_args @ ty_args') (t_args @ t_args') env' ret
  | ast ->
    begin match parse_expr env ast with
      | (Ty body) as res ->
        if t_args = [] then `Ty (ty_args, body)
        else _expected env "non_dependant type (or a term)" ast (Some res)
      | Term body -> `Term (ty_args, t_args, body)
      | res -> _expected env "term or a type" ast (Some res)
    end

(* High-level parsing functions *)
(* ************************************************************************ *)

let new_decl env t ?attr id =
  Util.enter_prof section;
  Util.info ~section "Typing declaration:@ @[<hov>%a :@ %a@]"
    Id.print id Ast.print t;
  let aux acc (Any (tag, v)) = Tag.add acc tag v in
  let tags =
    CCOpt.map (fun a ->
        Util.info ~section "Typing attribute:@ @[<hov>%a@]" Ast.print a;
        let l = parse_attr_and env a in
        List.fold_left aux Tag.empty l) attr
  in
  let res =
    match parse_sig env t with
    | `Ty_cstr n ->
      let c = Expr.Id.ty_fun ?tags (Id.full_name id) n in
      decl_ty_cstr id c (Declared (get_loc t));
      `Type_decl c
    | `Fun_ty (vars, args, ret) ->
      let f = Expr.Id.term_fun ?tags (Id.full_name id) vars args ret in
      decl_term id f (Declared (get_loc t));
      `Term_decl f
  in
  Util.exit_prof section;
  res

let new_def env t ?attr id =
  Util.enter_prof section;
  Util.info ~section "Typing definition:@ @[<hov>%a =@ %a@]"
    Id.print id Ast.print t;
  let res =
    match parse_fun [] [] env t with
    | `Ty (ty_args, body) ->
      def_ty id ty_args body;
      `Type_def (id, ty_args, body)
    | `Term (ty_args, t_args, body) ->
      def_term id ty_args t_args body;
      `Term_def (id, ty_args, t_args, body)
  in
  Util.exit_prof section;
  res

let new_formula env t =
  Util.enter_prof section;
  Util.info ~section "Typing top-level formula:@ %a" Ast.print t;
  let res = parse_formula env t in
  Util.exit_prof section;
  res

