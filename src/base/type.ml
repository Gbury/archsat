
(* Log&Module Init *)
(* ************************************************************************ *)

let section = Util.Section.make "type"
let log i fmt = Util.debug ~section i fmt

let stack = Backtrack.Stack.create (
    Util.Section.make ~parent:section "backtrack")

module M = Map.Make(String)
module H = Backtrack.HashtblBack(struct
    type t = string
    let hash = Hashtbl.hash
    let equal = Pervasives.(=)
  end)

(* Exceptions *)
(* ************************************************************************ *)

exception Typing_error of string * Ast.term

let _scope_err t = raise (Typing_error ("Scoping error", t))
let _expected s t = raise (Typing_error (
    Format.asprintf "Expected a %s" s, t))
let _bad_arity s n t = raise (Typing_error (
    Format.asprintf "Bad arity for operator '%s' (expected %d arguments)" s n, t))
let _type_mismatch t ty ty' ast = raise (Typing_error (
    Format.asprintf "Type Mismatch: '%a' has type %a, but an expression of type %a was expected"
      Expr.Print.term t Expr.Print.ty ty Expr.Print.ty ty', ast))

(* Global Environment *)
(* ************************************************************************ *)

(* Hashtable from symbol name to type constructors *)
let types = H.create stack
(* Hashtable from symbol name to function symbols *)
let constants = H.create stack
;;

(* Adding/finding elts *)
let add_type name c =
  try
    let c' = H.find types name in
    if not (Expr.Id.equal c c') then
      log 0 "Type constructor (%a) has already been defined, skipping delcaration (%a)"
        Expr.Debug.const_ttype c' Expr.Debug.const_ttype c
  with Not_found ->
    log 1 "New type constructor : %a" Expr.Debug.const_ttype c;
    H.add types name c

let find_ty_cstr name =
  try Some (H.find types name)
  with Not_found -> None

let add_cst name c =
  try
    let c' = H.find constants name in
    if not (Expr.Id.equal c c') then
      log 0 "Function (%a) has already been defined, skipping declaration (%a)"
        Expr.Debug.const_ty c Expr.Debug.const_ty c'
  with Not_found ->
    log 1 "New constant : %a" Expr.Debug.const_ty c;
    H.add constants name c

let find_cst (default_args, default_ret) name =
  try
    H.find constants name
  with Not_found ->
    let res = Expr.Id.term_fun name [] default_args default_ret in
    log 1 "Inferred constant : %a" Expr.Debug.const_ty res;
    H.add constants name res;
    res

(* Local Environment *)
(* ************************************************************************ *)

type builtin_symbols = string -> Expr.ty list -> Expr.term list ->
  [ `Ty of Expr.ttype Expr.function_descr Expr.id * Expr.ty list |
    `Term of Expr.ty Expr.function_descr Expr.id * Expr.ty list * Expr.term list] option

type env = {
  type_vars : Expr.Ty.t M.t;
  term_vars : Expr.Term.t M.t;
  prop_vars : Expr.Formula.t M.t;
  builtins : builtin_symbols;
}

let empty_env builtins = {
  type_vars = M.empty;
  term_vars = M.empty;
  prop_vars = M.empty;
  builtins;
}

let add_vars print map l new_var add =
  let q = Queue.create () in
  let add_var map v =
    try
      if M.mem Expr.(v.id_name) map then begin
        let v' = new_var Expr.(v.id_type) in
        Queue.add v' q;
        log 3 "Adding binding : %s -> %a" Expr.(v.id_name) print v';
        add Expr.(v.id_name) v' map
      end else
        raise Not_found
    with Not_found ->
      Queue.add v q;
      log 3 "Adding binding : %s -> %a" Expr.(v.id_name) print v;
      add Expr.(v.id_name) v map
  in
  let map' = List.fold_left add_var map l in
  List.rev (Queue.fold (fun acc x -> x :: acc) [] q), map'

let new_name pre =
  let i = ref 0 in
  (fun () -> incr i; pre ^ (string_of_int !i))

let new_ty_name = new_name "ty#"
let new_term_name = new_name "term#"

let add_type_vars ~status env l =
  let l', map = add_vars Expr.Debug.id_ttype env.type_vars l
      (fun Expr.Type -> Expr.Id.ttype (new_ty_name ()))
      (fun name v map -> M.add name (Expr.Ty.of_id ~status v) map)
  in
  l', { env with type_vars = map }

let add_type_var ~status env v = match add_type_vars ~status env [v] with | [v'], env' -> v', env' | _ -> assert false

let add_term_vars ~status env l =
  let l', map = add_vars Expr.Debug.id_ty env.term_vars l
      (fun ty -> Expr.Id.ty (new_term_name ()) ty)
      (fun name v map -> M.add name (Expr.Term.of_id ~status v) map)
  in
  l', { env with term_vars = map }

let add_let_term env name t = { env with term_vars = M.add name t env.term_vars }
let add_let_prop env name t = { env with prop_vars = M.add name t env.prop_vars }

let find_var map s =
  try
    Some (M.find s map)
  with Not_found ->
    None

let find_type_var env s = find_var env.type_vars s
let find_term_var env s = find_var env.term_vars s
let find_prop_var env s = find_var env.prop_vars s

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

(* Expression parsing *)
(* ************************************************************************ *)

let scope t f arg =
  match f arg with
  | Some res -> res
  | None -> _scope_err t

let parse_ttype_var = function
  | { Ast.term = Ast.Column (
      { Ast.term = Ast.Var s }, {Ast.term = Ast.Const Ast.Ttype}) } ->
    Expr.Id.ttype s
  | t -> _expected "a type variable" t

let parse_ty_cstr ~infer env ty_args s =
  match env.builtins s ty_args [] with
  | Some `Ty res -> Some res
  | _ -> begin match find_ty_cstr s with
      | Some x -> Some (x, ty_args)
      | None ->
        if infer && ty_args = [] then begin
          let res = Expr.Id.ty_fun s 0 in
          add_type s res;
          Some (res, [])
        end else
          None
    end

let rec parse_ty ~infer ~status env = function
  | { Ast.term = Ast.Var s} as t -> scope t (find_type_var env) s
  | { Ast.term = Ast.Const (Ast.String c)} as t ->
    let (f, args) = scope t (parse_ty_cstr ~infer env []) c in
    ty_apply t ~status f args
  | { Ast.term = Ast.App ({Ast.term = Ast.Const (Ast.String c) }, l) } as t ->
    let l' = List.map (parse_ty ~infer ~status env) l in
    let (f, args) = scope t (parse_ty_cstr ~infer env l') c in
    ty_apply t ~status f args
  | t -> _expected "type" t

let rec parse_sig ~status env = function
  | { Ast.term = Ast.Binding (Ast.AllTy, vars, t) } ->
    let typed_vars = List.map parse_ttype_var vars in
    let typed_vars, env' = add_type_vars ~status env typed_vars in
    let params, args, ret = parse_sig ~status env' t in
    (typed_vars @ params, args, ret)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, ret :: args) } ->
    [], List.map (parse_ty ~infer:true ~status env) args, parse_ty ~infer:true ~status env ret
  | t -> [], [], parse_ty ~infer:true ~status env t

let parse_ty_var ~status env = function
  | { Ast.term = Ast.Var s } ->
    Expr.Id.ty s Expr.Ty.base
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s }, ty) } ->
    Expr.Id.ty s (parse_ty ~infer:true ~status env ty)
  | t -> _expected "(typed) variable" t

let default_cst_ty n ret = (CCList.replicate n Expr.Ty.base, ret)

let parse_cst env ty_args t_args ret s =
  match env.builtins s ty_args t_args with
  | Some `Term ((cst, _, _) as res) ->
    log 10 "Builtin constant: %a" Expr.Debug.const_ty cst;
    res
  | _ ->
    let nargs = List.length t_args in
    (find_cst (default_cst_ty nargs ret) s), ty_args, t_args

let parse_let_var eval = function
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s}, t) } -> (s, eval t)
  | t -> _expected "'let' construct" t

let rec parse_args ~status env = function
  | [] -> [], []
  | (e :: r) as l ->
    try
      let ty_arg = parse_ty ~infer:false ~status env e in
      let ty_args, t_args = parse_args ~status env r in
      ty_arg :: ty_args, t_args
    with Typing_error _ ->
      let t_args = List.map (parse_term ~status Expr.Ty.base env) l in
      [], t_args

and parse_term ~status ret env = function
  | { Ast.term = Ast.Var s } as t -> scope t (find_term_var env) s
  | ({ Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) } as t)
  | ({ Ast.term = Ast.Const Ast.String s } as t) ->
    begin match find_term_var env s with
      | Some res -> res
      | None ->
        let f, ty_args, t_args = parse_cst env [] [] ret s in
        term_apply t ~status f ty_args t_args
    end
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, l) } as t ->
    let ty_args, t_args = parse_args ~status env l in
    let f, l, l' = parse_cst env ty_args t_args ret s in
    term_apply t ~status f l l'
  | { Ast.term = Ast.Binding (Ast.Let, vars, f) } ->
    let env' = List.fold_left (fun acc var ->
        let (s, t) = parse_let_var (parse_term ~status Expr.Ty.base env) var in
        add_let_term acc s t) env vars
    in
    parse_term ~status ret env' f
  | t -> _expected "term" t

let rec parse_quant_vars ~status env = function
  | [] -> [], [], env
  | (v :: r) as l ->
    try
      let ttype_var = parse_ttype_var v in
      let ttype_var, env' = add_type_var ~status env ttype_var in
      let l, l', env'' = parse_quant_vars ~status env' r in
      ttype_var :: l, l', env''
    with Typing_error _ ->
      let l' = List.map (parse_ty_var ~status env) l in
      let l'', env' = add_term_vars ~status env l' in
      [], l'', env'

let rec parse_formula ~status env = function

  (* Formulas *)
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.True }, []) }
  | { Ast.term = Ast.Const Ast.True } -> Expr.Formula.f_true
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.False }, []) }
  | { Ast.term = Ast.Const Ast.False } -> Expr.Formula.f_false
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.And}, l) } ->
    Expr.Formula.f_and (List.map (parse_formula ~status env) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Or}, l) } ->
    Expr.Formula.f_or (List.map (parse_formula ~status env) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Xor}, l) } as t ->
    begin match l with
      | [p; q] ->
        Expr.Formula.neg (
          Expr.Formula.equiv (parse_formula ~status env p) (parse_formula ~status env q))
      | _ -> _bad_arity "xor" 2 t
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Imply}, l) } as t ->
    begin match l with
      | [p; q] -> Expr.Formula.imply (parse_formula ~status env p) (parse_formula ~status env q)
      | _ -> _bad_arity "=>" 2 t
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Equiv}, l) } as t ->
    begin match l with
      | [p; q] -> Expr.Formula.equiv (parse_formula ~status env p) (parse_formula ~status env q)
      | _ -> _bad_arity "<=>" 2 t
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Not}, l) } as t ->
    begin match l with
      | [p] -> Expr.Formula.neg (parse_formula ~status env p)
      | _ -> _bad_arity "not" 1 t
    end

  (* Binders *)
  | { Ast.term = Ast.Binding (Ast.All, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars ~status env vars in
    Expr.Formula.allty ttype_vars (Expr.Formula.all ty_vars (parse_formula ~status env' f))
  | { Ast.term = Ast.Binding (Ast.Ex, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars ~status env vars in
    Expr.Formula.exty ttype_vars (Expr.Formula.ex ty_vars (parse_formula ~status env' f))
  | { Ast.term = Ast.Binding (Ast.Let, vars, f) } ->
    let env' = List.fold_left (fun acc var ->
        try
          let (s, t) = parse_let_var (parse_term ~status Expr.Ty.base env) var in
          log 2 "Let-binding : %s -> %a" s Expr.Debug.term t;
          add_let_term acc s t
        with Typing_error _ ->
          let (s, f) = parse_let_var (parse_formula ~status env) var in
          log 2 "Let-binding : %s -> %a" s Expr.Debug.formula f;
          add_let_prop acc s f
      ) env vars
    in
    parse_formula ~status env' f

  (* (Dis)Equality *)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Eq}, l) } as t ->
    begin match l with
      | [a; b] -> make_eq t (parse_term ~status Expr.Ty.base env a) (parse_term ~status Expr.Ty.base env b)
      | _ -> _bad_arity "=" 2 t
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Distinct}, args) } as t ->
    let l = CCList.diagonal (List.map (parse_term ~status Expr.Ty.base env) args) in
    Expr.Formula.f_and (List.map (fun (a, b) -> Expr.Formula.neg (make_eq t a b)) l)

  (* Possibly bound variables *)
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) }
  | { Ast.term = Ast.Const Ast.String s } | { Ast.term = Ast.Var s } as t ->
    begin match find_prop_var env s with
      | Some res -> res
      | None -> make_pred t (parse_term ~status Expr.Ty.prop env t)
    end

  (* Generic terms *)
  | { Ast.term = Ast.App _ }
  | { Ast.term = Ast.Const _ } as t ->
    make_pred t (parse_term ~status Expr.Ty.prop env t)

  (* Absurd case *)
  | t -> _expected "formula" t

(* Exported functions *)
(* ************************************************************************ *)

let new_type_def (sym, n) =
  Util.enter_prof section;
  begin match sym with
    | Ast.String s -> add_type s (Expr.Id.ty_fun s n)
    | _ -> log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym
  end;
  Util.exit_prof section

let new_const_def builtins (sym, t) =
  Util.enter_prof section;
  begin match sym with
    | Ast.String s ->
      let params, args, ret = parse_sig ~status:Expr.Status.hypothesis (empty_env builtins) t in
      add_cst s (Expr.Id.term_fun s params args ret)
    | _ ->
      log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym
  end;
  Util.exit_prof section

let parse ~goal builtins t =
  Util.enter_prof section;
  let status = if goal then Expr.Status.goal else Expr.Status.hypothesis in
  let f = parse_formula ~status (empty_env builtins) t in
  log 1 "New expr : %a" Expr.Debug.formula f;
  Util.exit_prof section;
  f

