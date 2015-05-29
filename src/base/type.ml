
(* Log&Module Init *)
(* ************************************************************************ *)

let log_section = Util.Section.make "type"
let log i fmt = Util.debug ~section:log_section i fmt
let stack = Backtrack.Stack.create ()

module M = Map.Make(String)
module H = Backtrack.HashtblBack(struct
    type t = string
    let hash = Hashtbl.hash
    let equal = Pervasives.(=)
  end)

(* Exceptions *)
(* ************************************************************************ *)

exception Typing_error of string * Ast.term
exception Scoping_error of string
exception Bad_arity of string * int * Ast.term list

(* Global Environment *)
(* ************************************************************************ *)

(* Hashtable from symbol name to type constructors *)
let types = H.create stack
(* Hashtable from symbol name to function symbols *)
let constants = H.create stack
;;

(* Builtin constants *)
H.add types "$o" Expr.Id.prop;;
H.add types "$i" Builtin.i_cstr;;

(* Adding/finding elts *)
let add_type name c =
  try
    let c' = H.find types name in
    if not (Expr.Id.equal c c') then
      log 0 "Incoherent type decl for '%s' : %a <> %a" name
        Expr.Debug.fun_ttype Expr.(c.id_type) Expr.Debug.fun_ttype Expr.(c'.id_type)
  with Not_found ->
    log 1 "New type constructor : %a" Expr.Debug.const_ttype c;
    H.add types name c

let add_cst name c =
  try
    let c' = H.find constants name in
    if not (Expr.Id.equal c c') then
      log 0 "Incoherent type decl for '%s' : %a <> %a" name
        Expr.Debug.fun_ty Expr.(c.id_type) Expr.Debug.fun_ty Expr.(c'.id_type)
  with Not_found ->
    log 1 "New constant : %a" Expr.Debug.const_ty c;
    H.add constants name c

let find_ty_cstr name =
  try
    H.find types name
  with Not_found ->
    raise (Scoping_error name)

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
  [ `Ty of Expr.ttype Expr.function_descr Expr.id |
    `Term of Expr.ty Expr.function_descr Expr.id ] option

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
    M.find s map
  with Not_found ->
    raise (Scoping_error s)

let find_type_var env s = find_var env.type_vars s
let find_term_var env s = find_var env.term_vars s
let find_prop_var env s = find_var env.prop_vars s

(* Expression parsing *)
(* ************************************************************************ *)

let parse_ttype_var = function
  | { Ast.term = Ast.Column (
      { Ast.term = Ast.Var s }, {Ast.term = Ast.Const Ast.Ttype}) } ->
    Expr.Id.ttype s
  | t -> raise (Typing_error ("Expected a type variable", t))

let parse_ty_cstr env ty_args t_args s =
  match env.builtins s ty_args t_args with
  | Some `Ty f -> f
  | _ -> find_ty_cstr s

let rec parse_ty ~status env = function
  | { Ast.term = Ast.Var s} -> find_type_var env s
  | { Ast.term = Ast.Const (Ast.String c)} -> Expr.Ty.apply ~status (find_ty_cstr c) []
  | { Ast.term = Ast.App ({Ast.term = Ast.Const (Ast.String c) }, l) } ->
    let l' = List.map (parse_ty ~status env) l in
    Expr.Ty.apply ~status (parse_ty_cstr env l' [] c) l'
  | t -> raise (Typing_error ("Expected a type", t))

let rec parse_sig ~status env = function
  | { Ast.term = Ast.Binding (Ast.AllTy, vars, t) } ->
    let typed_vars = List.map parse_ttype_var vars in
    let typed_vars, env' = add_type_vars ~status env typed_vars in
    let params, args, ret = parse_sig ~status env' t in
    (typed_vars @ params, args, ret)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, ret :: args) } ->
    [], List.map (parse_ty ~status env) args, parse_ty ~status env ret
  | t -> [], [], parse_ty ~status env t

let parse_ty_var ~status env = function
  | { Ast.term = Ast.Var s } ->
    Expr.Id.ty s Builtin.type_i
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s }, ty) } ->
    Expr.Id.ty s (parse_ty ~status env ty)
  | t -> raise (Typing_error ("Expected a (typed) variable", t))

let default_cst_ty n ret = (CCList.replicate n Builtin.type_i, ret)

let parse_cst env ty_args t_args ret s =
  match env.builtins s ty_args t_args with
  | Some `Term f -> f
  | _ ->
    let nargs = List.length t_args in
    find_cst (default_cst_ty nargs ret) s

let parse_let_var eval = function
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s}, t) } -> (s, eval t)
  | t -> raise (Typing_error ("Expected a 'let' construct", t))

let rec parse_args ~status env = function
  | [] -> [], []
  | (e :: r) as l ->
    try
      let ty_arg = parse_ty ~status env e in
      let ty_args, t_args = parse_args ~status env r in
      ty_arg :: ty_args, t_args
    with Typing_error _ | Scoping_error _ ->
      let t_args = List.map (parse_term ~status Builtin.type_i env) l in
      [], t_args

and parse_term ~status ret env = function
  | { Ast.term = Ast.Var s } -> find_term_var env s
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) }
  | { Ast.term = Ast.Const Ast.String s } ->
    begin try
        find_term_var env s
      with Scoping_error _ ->
        Expr.Term.apply ~status (parse_cst env [] [] ret s) [] []
    end
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, l) } ->
    let ty_args, t_args = parse_args ~status env l in
    let f = parse_cst env ty_args t_args ret s in
    Expr.Term.apply ~status f ty_args t_args
  | { Ast.term = Ast.Binding (Ast.Let, vars, f) } ->
    let env' = List.fold_left (fun acc var ->
        let (s, t) = parse_let_var (parse_term ~status Builtin.type_i env) var in
        add_let_term acc s t) env vars
    in
    parse_term ~status ret env' f
  | t -> raise (Typing_error ("Expected a term", t))

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
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Xor}, l) } ->
    assert false
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Imply}, l) } ->
    begin match l with
      | [p; q] -> Expr.Formula.imply (parse_formula ~status env p) (parse_formula ~status env q)
      | _ -> raise (Bad_arity ("=>", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Equiv}, l) } ->
    begin match l with
      | [p; q] -> Expr.Formula.equiv (parse_formula ~status env p) (parse_formula ~status env q)
      | _ -> raise (Bad_arity ("<=>", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Not}, l) } ->
    begin match l with
      | [p] -> Expr.Formula.neg (parse_formula ~status env p)
      | _ -> raise (Bad_arity ("not", 1, l))
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
          let (s, t) = parse_let_var (parse_term ~status Builtin.type_i env) var in
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
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Eq}, l) } ->
    begin match l with
      | [a; b] -> Expr.Formula.eq (parse_term ~status Builtin.type_i env a) (parse_term ~status Builtin.type_i env b)
      | _ -> raise (Bad_arity ("=", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Distinct}, args) } ->
    let l = CCList.diagonal (List.map (parse_term ~status Builtin.type_i env) args) in
    Expr.Formula.f_and (List.map (fun (a, b) -> Expr.Formula.neg (Expr.Formula.eq a b)) l)

  (* Possibly bound variables *)
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) }
  | { Ast.term = Ast.Const Ast.String s } | { Ast.term = Ast.Var s } as t ->
    begin try find_prop_var env s
      with Scoping_error _ -> Expr.Formula.pred (parse_term ~status Expr.Ty.prop env t) end

  (* Generic terms *)
  | { Ast.term = Ast.App _ }
  | { Ast.term = Ast.Const _ } as t ->
    Expr.Formula.pred (parse_term ~status Expr.Ty.prop env t)

  (* Absurd case *)
  | t -> raise (Typing_error ("Expected a formula", t))

(* Exported functions *)
(* ************************************************************************ *)

let new_type_def (sym, n) =
  match sym with
  | Ast.String s -> add_type s (Expr.Id.ty_fun s n)
  | _ ->
    log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let new_const_def builtins (sym, t) =
  match sym with
  | Ast.String s ->
    let params, args, ret = parse_sig ~status:Expr.Status.hypothesis (empty_env builtins) t in
    add_cst s (Expr.Id.term_fun s params args ret)
  | _ ->
    log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let parse ~goal builtins t =
  let status = if goal then Expr.Status.goal else Expr.Status.hypothesis in
  let f = parse_formula ~status (empty_env builtins) t in
  log 1 "New expr : %a" Expr.Debug.formula f;
  f

