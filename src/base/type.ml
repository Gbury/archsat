
(* Log&Module Init *)
(* ************************************************************************ *)

let section = Util.Section.make "type"
let log i fmt = Util.debug ~section i fmt

let stack = Backtrack.Stack.create (
    Util.Section.make ~parent:section "backtrack")

module Ast = Dolmen.Term
module Id = struct
  type t = Ast.id
  let hash = Hashtbl.hash
  let equal = Pervasives.(=)
  let compare = Pervasives.compare
end
module M = Map.Make(Id)
module H = Backtrack.HashtblBack(Id)

(* Types *)
(* ************************************************************************ *)

(* The type of potentially expected result type for parsingan expression *)
type expect =
  | Nothing
  | Type
  | Typed of Expr.ty

(* The type returned after parsing an expression. *)
type res =
  | Ttype
  | Ty of Expr.ty
  | Term of Expr.term
  | Formula of Expr.formula

(* Exceptions *)
(* ************************************************************************ *)

(* Internal exception *)
exception Found of Ast.t

(* Exception for typing errors *)
exception Typing_error of string * Ast.t

(* Convenience functions *)
let _expected s t = raise (Typing_error (
    Format.asprintf "Expected a %s" s, t))
let _bad_arity s n t = raise (Typing_error (
    Format.asprintf "Bad arity for operator '%s' (expected %d arguments)" s n, t))
let _type_mismatch t ty ty' ast = raise (Typing_error (
    Format.asprintf "Type Mismatch: '%a' has type %a, but an expression of type %a was expected"
      Expr.Print.term t Expr.Print.ty ty Expr.Print.ty ty', ast))
let _fo_term s t = raise (Typing_error (
    Format.asprintf "Let-bound variable '%s' is applied to terms" s.Ast.name, t))

(* Global Environment *)
(* ************************************************************************ *)

(* Global identifier table; stores declared types and aliases. *)
let global_env = H.create stack

let find_global name =
  try H.find global_env name
  with Not_found -> `Not_found

(* Symbol declarations *)
let decl_ty_cstr id c =
  if H.mem global_env id then
    log 0 "Symbol '%s' has already been defined, overwriting previous definition" id.Ast.name;
  H.add global_env id (`Ty c);
  log 1 "New type constructor : %a" Expr.Debug.const_ttype c

let decl_term id c =
  if H.mem global_env id then
    log 0 "Symbol '%s' has already been defined, overwriting previous definition" id.Ast.name;
  H.add global_env id (`Term c);
  log 1 "New constant : %a" Expr.Debug.const_ty c

(* Symbol definitions *)
let def_ty id args body =
  if H.mem global_env id then
    log 0 "Symbol '%s' has already been defined, overwriting previous definition" id.Ast.name;
  H.add global_env id (`Ty_alias (args, body));
  log 1 "New type alias: %s(%a) = %a" id.Ast.name
    (CCPrint.list ~start:"" ~stop:"" ~sep:"," Expr.Debug.id_ttype) args
    Expr.Debug.ty body

let def_term id ty_args args body =
  if H.mem global_env id then
    log 0 "Symbol '%s' has already been defined, overwriting previous definition" id.Ast.name;
  H.add global_env id (`Term_alias (ty_args, args, body));
  log 1 "New type alias: %s(%a;%a) = %a" id.Ast.name
    (CCPrint.list ~start:"" ~stop:"" ~sep:"," Expr.Debug.id_ttype) ty_args
    (CCPrint.list ~start:"" ~stop:"" ~sep:"," Expr.Debug.id_ty) args
    Expr.Debug.term body

(* Local Environment *)
(* ************************************************************************ *)

(* Builtin symbols, i.e symbols understood by some theories,
   but which do not have specific syntax, so end up as special
   cases of application. *)
type builtin_symbols = env -> string -> Ast.t list -> res option

(* The local environments used for type-checking. *)
and env = {

  (* local variables (mostly quantified variables) *)
  type_vars : (Expr.ttype Expr.id)  M.t;
  term_vars : (Expr.ty Expr.id)     M.t;

  (* Bound variables (through let constructions) *)
  term_lets : Expr.term     M.t;
  prop_lets : Expr.formula  M.t;

  (* The current builtin symbols *)
  builtins : builtin_symbols;

  (* Typing options *)
  expect   : expect;
  status   : Expr.status;
}

(* Make a new empty environment *)
let empty_env
    ?(expect=Typed Expr.Ty.prop)
    ?(status=Expr.Status.hypothesis)
    builtins = {
  type_vars = M.empty;
  term_vars = M.empty;
  term_lets = M.empty;
  prop_lets = M.empty;
  builtins;
  expect; status;
}

(* Generic function for adding new variables to anenvironment.
   Tries and add a binding from [v.id_name] to [v] in [map] using [add],
   however, if a binding already exists, use [new_var] to create a
   new variable to bind to [v.id_name].
   Returns the identifiers actually bound, and the new map. *)
let add_var print new_var add map id v =
  let v' =
    if M.mem id map then
      new_var id.Ast.name
    else
      v
  in
  log 3 "Adding binding : %s -> %a" Expr.(v.id_name) print v';
  v', add Expr.(v.id_name) v' map

(* Generate new fresh names for shadowed variables *)
let new_name pre =
  let i = ref 0 in
  (fun () -> incr i; pre ^ (string_of_int !i))

let new_ty_name = new_name "ty#"
let new_term_name = new_name "term#"

(* Add local variables to environment *)
let add_type_var env id v =
  let v' =
    if M.mem id env.type_vars then
      Expr.Id.ttype (new_ty_name ())
    else
      v
  in
  log 3 "New binding : %s -> %a" id.Ast.name Expr.Debug.id_ttype v';
  v', { env with type_vars = M.add id v' env.type_vars }

let add_type_vars env l =
  let l', env' = List.fold_left (fun (l, acc) (id, v) ->
      let v', acc' = add_type_var acc id v in
      v' :: l, acc') ([], env) l in
  List.rev l', env'

let add_term_var env id v =
  let v' =
    if M.mem id env.type_vars then
      Expr.Id.ty (new_term_name ()) Expr.(v.id_type)
    else
      v
  in
  log 3 "New binding : %s -> %a" id.Ast.name Expr.Debug.id_ty v';
  v', { env with term_vars = M.add id v' env.term_vars }

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
let add_let_term env name t = { env with term_lets = M.add name t env.term_lets }
let add_let_prop env name t = { env with prop_lets = M.add name t env.prop_lets }

let find_let env name =
  try `Term (M.find name env.term_lets)
  with Not_found ->
    begin
      try
        `Prop (M.find name env.prop_lets)
      with Not_found ->
        `Not_found
    end

(* Wrappers for expression building *)
(* ************************************************************************ *)

let arity f =
  List.length Expr.(f.id_type.fun_vars) +
  List.length Expr.(f.id_type.fun_args)

let ty_apply ast_term ~status f args =
  try
    Expr.Ty.apply ~status f args
  with Expr.Bad_ty_arity _ ->
    _bad_arity Expr.(f.id_name) (arity f) ast_term

let term_apply ast_term ~status f ty_args t_args =
  try
    Expr.Term.apply ~status f ty_args t_args
  with
  | Expr.Bad_arity _ ->
    _bad_arity Expr.(f.id_name) (arity f) ast_term
  | Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch t ty ty' ast_term

let ty_subst ast_term name args f_args body =
  let aux s v ty = Expr.Subst.Id.bind v ty s in
  match List.fold_left2 aux Expr.Subst.empty f_args args with
  | subst ->
    Expr.Ty.subst subst body
  | exception Invalid_argument _ ->
    _bad_arity name (List.length f_args) ast_term

let ty_subst ast_term name args f_args body =
  let aux s v ty = Expr.Subst.Id.bind v ty s in
  match List.fold_left2 aux Expr.Subst.empty f_args args with
  | subst ->
    Expr.Ty.subst subst body
  | exception Invalid_argument _ ->
    _bad_arity name (List.length f_args) ast_term

let make_eq ast_term a b =
  try
    Expr.Formula.eq a b
  with Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch t ty ty' ast_term

let make_pred ast_term p =
  try
    Expr.Formula.pred p
  with Expr.Type_mismatch (t, ty, ty') ->
    _type_mismatch t ty ty' ast_term

let infer env s args =
  match env.expect with
  | Nothing -> `Nothing
  | Type ->
    let n = List.length args in
    `Ty (Expr.Id.ty_fun s n)
  | Typed ty ->
    let n = List.length args in
    `Term (Expr.Id.term_fun s [] (CCList.replicate n Expr.Ty.base) ty)

(* Expression parsing *)
(* ************************************************************************ *)

let rec parse_expr (env : env) = function

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
        Formula (
          Expr.Formula.neg (
            Expr.Formula.equiv
              (parse_formula env p)
              (parse_formula env q)
          ))
      | _ -> _bad_arity "xor" 2 t
    end

  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Imply}, l) } as t ->
    begin match l with
      | [p; q] ->
        Formula (
          Expr.Formula.imply
            (parse_formula env p)
            (parse_formula env q)
        )
      | _ -> _bad_arity "=>" 2 t
    end

  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv}, l) } as t ->
    begin match l with
      | [p; q] ->
        Formula (
          Expr.Formula.equiv
            (parse_formula env p)
            (parse_formula env q)
        )
      | _ -> _bad_arity "<=>" 2 t
    end

  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Not}, l) } as t ->
    begin match l with
      | [p] ->
        Formula (Expr.Formula.neg (parse_formula env p))
      | _ -> _bad_arity "not" 1 t
    end

  (* Binders *)
  | { Ast.term = Ast.Binder (Ast.All, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars env vars in
    Formula (
      Expr.Formula.allty ttype_vars
        (Expr.Formula.all ty_vars (parse_formula env' f))
    )

  | { Ast.term = Ast.Binder (Ast.Ex, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars env vars in
    Formula (
      Expr.Formula.exty ttype_vars
        (Expr.Formula.ex ty_vars (parse_formula env' f))
    )

  | { Ast.term = Ast.Binder (Ast.Let, vars, f) } ->
    parse_let env f vars

  (* (Dis)Equality *)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Eq}, l) } as t ->
    begin match l with
      | [a; b] ->
        Formula (
          make_eq t
            (parse_term env a)
            (parse_term env b)
        )
      | _ -> _bad_arity "=" 2 t
    end

  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Distinct}, args) } as t ->
    let l' = List.map (parse_term { env with expect = Typed Expr.Ty.base}) args in
    let l'' = CCList.diagonal l' in
    Formula (
      Expr.Formula.f_and
        (List.map (fun (a, b) -> Expr.Formula.neg (make_eq t a b)) l'')
    )

  (* General case: application *)
  | ({ Ast.term = Ast.Symbol s } as t) ->
    parse_app env t s []
  | { Ast.term = Ast.App ({ Ast.term = Ast.Symbol s }, l) } as t ->
    parse_app env t s l

  | t -> raise (Typing_error ("Couldn't parse the expression", t))

and parse_var env = function
  | { Ast.term = Ast.Colon ({ Ast.term = Ast.Symbol s }, e) } ->
    begin match parse_expr env e with
      | Ttype -> `Ty (s, Expr.Id.ttype s.Ast.name)
      | Ty ty -> `Term (s, Expr.Id.ty s.Ast.name ty)
      | _ -> _expected "type (or Ttype)" e
    end
  | { Ast.term = Ast.Symbol s } ->
    begin match env.expect with
      | Nothing -> assert false
      | Type -> `Ty (s, Expr.Id.ttype s.Ast.name)
      | Typed ty -> `Term (s, Expr.Id.ty s.Ast.name ty)
    end
  | t -> _expected "(typed) variable" t

and parse_quant_vars env l =
  let ttype_vars, typed_vars, env' = List.fold_left (
      fun (l1, l2, acc) v ->
        match parse_var acc v with
        | `Ty (id, v') ->
          let v'', acc' = add_type_var env id v' in
          (v'' :: l1, l2, acc')
        | `Term (id, v') ->
          let v'', acc' = add_term_var env id v' in
          (l1, v'' :: l2, acc')
    ) ([], [], { env with expect = Typed Expr.Ty.base }) l in
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
          | _ -> _expected "term of formula" e
        end
      | t -> _expected "let-binding" t
    end

and parse_app env ast s args =
  match find_let env s with
  | `Term t ->
    if args = [] then Term t
    else _fo_term s ast
  | `Prop p ->
    if args = [] then Formula p
    else _fo_term s ast
  | `Not_found ->
    begin match find_var env s with
      | `Ty f ->
        if args = [] then Ty (Expr.Ty.of_id f)
        else _fo_term s ast
      | `Term f ->
        if args = [] then Term (Expr.Term.of_id f)
        else _fo_term s ast
      | `Not_found ->
        begin match find_global s with
          | `Ty f -> parse_app_ty env ast f args
          | `Term f -> parse_app_term env ast f args
          | `Ty_alias (args, body) ->
            try
              ()
            with
          | `Not_found ->
            begin match env.builtins env s args with
              | Some res -> res
              | None ->
                begin match infer env s args with
                  | `Ty f -> parse_app_ty env ast f args
                  | `Term f -> parse_app_term env ast f args
                  | `Nothing ->
                    raise (Typing_error (
                        Format.asprintf "Scoping error: '%s' not found" s, ast))
                end
            end
        end
    end

and parse_app_ty env ast f args =
  let l = List.map (parse_ty env) args in
  Ty (ty_apply ast ~status:env.status f l)

and parse_app_term env ast f args =
  let n = List.length Expr.(f.id_type.fun_vars) in
  let ty_l, t_l = CCList.take_drop n args in
  let ty_args = List.map (parse_ty env) ty_l in
  let t_args = List.map (parse_term env) t_l in
  Term (term_apply ast ~status:env.status f ty_args t_args)

and parse_ty env ast =
  match parse_expr env ast with
  | Ty ty -> ty
  | _ -> _expected "type" ast

and parse_term env ast =
  match parse_expr env ast with
  | Term t -> t
  | _ -> _expected "term" ast

and parse_formula env ast =
  match parse_expr env ast with
  | Formula p -> p
  | _ -> _expected "formula" ast

let parse_ttype_var env t =
  match parse_var env t with
  | `Ty (id, v) -> (id, v)
  | `Term _ -> _expected "type variable" t

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
              "Type constructor signatures cannot have quantified type variables", h))
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
                    "Type constructor signatures cannot have non-ttype arguments,", err))
          end
      end
    | Ty ret ->
      let aux acc = function
        | (_, Ty t) -> t :: acc
        | (ast, _) -> raise (Found ast)
      in
      begin
        match List.fold_left aux [] ty_args with
        | exception Found err -> _expected "type" err
        | l -> `Fun_ty (List.map snd ttype_vars, List.rev l, ret)
      end
    | _ -> _expected "Ttype of type" t
    end

and parse_sig_args env l =
  CCList.flat_map (parse_sig_arg env) l

and parse_sig_arg env = function
  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Product}, l) } ->
    List.map (fun x -> x, parse_expr env x) l
  | t ->
    [t, parse_expr env t]

and parse_sig = parse_sig_quant

let rec parse_fun ty_args t_args env = function
  | { Ast.term = Ast.Binder (Ast.Fun, l, ret) } ->
    let ty_args', t_args', env' = parse_quant_vars env l in
    parse_fun (ty_args @ ty_args') (t_args @ t_args') env' ret
  | ast ->
    begin match parse_expr env ast with
      | Ttype -> raise (Typing_error ("Cannot redefine Ttype", ast))
      | Ty _ -> assert false
      | _ -> assert false
    end

(* High-level parsing functions *)
(* ************************************************************************ *)

let new_decl ~builtin name t =
  Util.enter_prof section;
  let env = empty_env builtin in
  begin match parse_sig env t with
    | `Ty_cstr n -> decl_ty_cstr name (Expr.Id.ty_fun name n)
    | `Fun_ty (vars, args, ret) ->
      decl_term name (Expr.Id.term_fun name vars args ret)
  end;
  Util.exit_prof section

let new_def ~builtin name t =
  Util.enter_prof section;
  let env = empty_env builtin in
  begin match parse_fun [] [] env t with
    | _ -> assert false
  end;
  Util.exit_prof section

(*
let parse ~goal builtins t =
  Util.enter_prof section;
  let status = if goal then Expr.Status.goal else Expr.Status.hypothesis in
  let f = parse_formula ~status (empty_env builtins) t in
  log 1 "New expr : %a" Expr.Debug.formula f;
  Util.exit_prof section;
  f
*)

