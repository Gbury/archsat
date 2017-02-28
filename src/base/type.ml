
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
type res =
  | Ttype   : res
  | Ty      : Expr.ty -> res
  | Term    : Expr.term -> res
  | Formula : Expr.formula -> res
  | Tag     : 'a Tag.t * 'a -> res

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

let expect env expect = { env with expect = expect }

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
exception Found of Ast.t

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
let _expected env s t =
  let msg = Format.asprintf "Expected a %s" s in
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

let _fo_term env s t =
  let msg = Format.asprintf "Let-bound variable '%a' is applied to terms" Id.print s in
  raise (Typing_error (msg, env, t))

let _type_mismatch env t ty ty' ast =
  let msg = Format.asprintf
      "Type Mismatch: an expression of type %a was expected, but '%a' has type %a%a"
      Expr.Print.ty ty' Expr.Print.term t Expr.Print.ty ty (mk_expl ", because:" env) t
  in
  raise (Typing_error (msg, env, ast))

(* Wrappers for expression building *)
(* ************************************************************************ *)

let arity f =
  List.length Expr.(f.id_type.fun_vars) +
  List.length Expr.(f.id_type.fun_args)

let ty_apply env ast f args =
  try
    Expr.Ty.apply ~status:env.status f args
  with Expr.Bad_ty_arity _ ->
    _bad_term_arity env f (arity f) ast

let term_apply env ast f ty_args t_args =
  try
    Expr.Term.apply ~status:env.status f ty_args t_args
  with
  | Expr.Bad_arity _ ->
    _bad_term_arity env f (arity f) ast
  | Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch env t ty ty' ast

let ty_subst env ast_term id args f_args body =
  match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_args args with
  | subst ->
    Expr.Ty.subst subst body
  | exception Invalid_argument _ ->
    _bad_id_arity env id (List.length f_args) ast_term

let term_subst env ast_term id ty_args t_args f_ty_args f_t_args body =
  match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_ty_args ty_args with
  | ty_subst ->
    begin
      match List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty f_t_args t_args with
      | t_subst ->
        Expr.Term.subst ty_subst t_subst body
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
  | Tag _ -> raise (Typing_error ("Cannot tag a tag", env, ast))
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
        parse_quant_vars { env with expect = Typed Expr.Ty.base } vars in
      Formula (
        Expr.Formula.allty ttype_vars
          (Expr.Formula.all ty_vars (parse_formula env' f))
      )

    | { Ast.term = Ast.Binder (Ast.Ex, vars, f) } ->
      let ttype_vars, ty_vars, env' =
        parse_quant_vars { env with expect = Typed Expr.Ty.base } vars in
      Formula (
        Expr.Formula.exty ttype_vars
          (Expr.Formula.ex ty_vars (parse_formula env' f))
      )

    (* (Dis)Equality *)
    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Eq}, l) } as t ->
      begin match l with
        | [a; b] ->
          Formula (
            make_eq env t
              (parse_term env a)
              (parse_term env b)
          )
        | _ -> _bad_op_arity env "=" 2 t
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Distinct}, args) } as t ->
      let l' = List.map (parse_term env) args in
      let l'' = CCList.diagonal l' in
      Formula (
        Expr.Formula.f_and
          (List.map (fun (a, b) -> Expr.Formula.neg (make_eq env t a b)) l'')
      )

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
  parse_attr env res t t.Ast.attr

and parse_attr env res ast = function
  | [] -> res
  | a :: r ->
    begin match parse_expr { env with expect = Nothing } a with
      | Tag (tag, v) ->
        apply_tag env ast tag v res;
        parse_attr env res ast r
      | _ ->
        _expected env "tag" a
      | exception (Typing_error (msg, _, t)) ->
        Util.warn ~section "%a while parsing an attribute:@\n%s"
          Dolmen.ParseLocation.fmt (get_loc t) msg;
        parse_attr env res ast r
    end

and parse_var env = function
  | { Ast.term = Ast.Colon ({ Ast.term = Ast.Symbol s }, e) } ->
    begin match parse_expr env e with
      | Ttype -> `Ty (s, Expr.Id.ttype (Id.full_name s))
      | Ty ty -> `Term (s, Expr.Id.ty (Id.full_name s) ty)
      | _ -> _expected env "type (or Ttype)" e
    end
  | { Ast.term = Ast.Symbol s } ->
    begin match env.expect with
      | Nothing -> assert false
      | Type -> `Ty (s, Expr.Id.ttype (Id.full_name s))
      | Typed ty -> `Term (s, Expr.Id.ty (Id.full_name s) ty)
    end
  | t -> _expected env "(typed) variable" t

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
          | _ -> _expected env "term of formula" e
        end
      | t -> _expected env "let-binding" t
    end

and parse_app env ast s args =
  match find_let env s with
  | `Term t ->
    if args = [] then Term t
    else _fo_term env s ast
  | `Prop p ->
    if args = [] then Formula p
    else _fo_term env s ast
  | `Not_found ->
    begin match find_var env s with
      | `Ty f ->
        if args = [] then Ty (Expr.Ty.of_id f)
        else _fo_term env s ast
      | `Term f ->
        if args = [] then Term (Expr.Term.of_id f)
        else _fo_term env s ast
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
                Util.info ~section
                  "Looking up '%a' failed, possibilities were:@ @[<hov>%a@]"
                  Id.print s (suggest ~limit:1 env) s;
                begin match infer env s args (get_loc ast) with
                  | Some Ty_fun f -> parse_app_ty env ast f args
                  | Some Term_fun f -> parse_app_term env ast f args
                  | None ->
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
  let n = List.length Expr.(f.id_type.fun_vars) in
  let ty_l, t_l = CCList.take_drop n args in
  let ty_args = List.map (parse_ty env) ty_l in
  let t_args = List.map (parse_term env) t_l in
  Term (term_apply env ast f ty_args t_args)

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
  match parse_expr { env with expect = Type } ast with
  | Ty ty -> ty
  | _ -> _expected env "type" ast

and parse_term env ast =
  match parse_expr { env with expect = Typed Expr.Ty.base } ast with
  | Term t -> t
  | _ -> _expected env "term" ast

and parse_formula env ast =
  match parse_expr { env with expect = Typed Expr.Ty.prop } ast with
  | Term t when Expr.(Ty.equal Ty.prop t.t_type) ->
    make_pred env ast t
  | Formula p -> p
  | _ -> _expected env "formula" ast

let parse_ttype_var env t =
  match parse_var env t with
  | `Ty (id, v) -> (id, v, get_loc t)
  | `Term _ -> _expected env "type variable" t

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
              | (ast, _) -> raise (Found ast)
            in
            begin
              match List.fold_left aux 0 ty_args with
              | n -> `Ty_cstr n
              | exception Found err ->
                raise (Typing_error (
                    Format.asprintf
                      "Type constructor signatures cannot have non-ttype arguments,", env, err))
            end
        end
      | Ty ret ->
        let aux acc = function
          | (_, Ty t) -> t :: acc
          | (ast, _) -> raise (Found ast)
        in
        begin
          match List.fold_left aux [] ty_args with
          | exception Found err -> _expected env "type" err
          | l -> `Fun_ty (List.map snd ttype_vars, List.rev l, ret)
        end
      | _ -> _expected env "Ttype of type" t
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
      | Tag _ -> raise (Typing_error ("Cannot define a tag", env, ast))
      | Ttype -> raise (Typing_error ("Cannot redefine Ttype", env, ast))
      | Ty body ->
        if t_args = [] then `Ty (ty_args, body)
        else _expected env "term" ast
      | Term body -> `Term (ty_args, t_args, body)
      | Formula _ -> _expected env "type or term" ast
    end

(* High-level parsing functions *)
(* ************************************************************************ *)

let new_decl env t id =
  Util.enter_prof section;
  Util.info ~section "Typing declaration:@ @[<hov>%a :@ %a@]"
    Id.print id Ast.print t;
  let res =
    match parse_sig env t with
    | `Ty_cstr n ->
      let c = Expr.Id.ty_fun (Id.full_name id) n in
      decl_ty_cstr id c (Declared (get_loc t));
      `Type_decl c
    | `Fun_ty (vars, args, ret) ->
      let f = Expr.Id.term_fun (Id.full_name id) vars args ret in
      decl_term id f (Declared (get_loc t));
      `Term_decl f
  in
  Util.exit_prof section;
  res

let new_def env t id =
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

