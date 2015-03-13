
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

exception Typing_error
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
H.add types "$o" Expr.prop_cstr;;
H.add types "$i" Builtin.i_cstr;;

(* Adding/finding elts *)
let add_type name c =
  try
    let c' = H.find types name in
    if not (Expr.Var.equal c c') then
      log 0 "Incoherent type decl for '%s' : %a <> %a" name
        Expr.debug_fun_ttype Expr.(c.var_type) Expr.debug_fun_ttype Expr.(c'.var_type)
  with Not_found ->
    log 1 "New type constructor : %a" Expr.debug_const_ttype c;
    H.add types name c

let add_cst name c =
  try
    let c' = H.find constants name in
    if not (Expr.Var.equal c c') then
      log 0 "Incoherent type decl for '%s' : %a <> %a" name
        Expr.debug_fun_ty Expr.(c.var_type) Expr.debug_fun_ty Expr.(c'.var_type)
  with Not_found ->
    log 1 "New constant : %a" Expr.debug_const_ty c;
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
    let res = Expr.term_const name [] default_args default_ret in
    log 1 "Inferred constant : %a" Expr.debug_const_ty res;
    H.add constants name res;
    res

(* Local Environment *)
(* ************************************************************************ *)

type env = {
  type_vars : Expr.Ty.t M.t;
  term_vars : Expr.Term.t M.t;
  prop_vars : Expr.Formula.t M.t;
}

let empty_env = {
  type_vars = M.empty;
  term_vars = M.empty;
  prop_vars = M.empty;
}

let add_vars print map l new_var add =
  let q = Queue.create () in
  let add_var map v =
    try
      if M.mem Expr.(v.var_name) map then begin
        let v' = new_var Expr.(v.var_type) in
        Queue.add v' q;
        log 3 "Adding binding : %s -> %a" Expr.(v.var_name) print v';
        add Expr.(v.var_name) v' map
      end else
        raise Not_found
    with Not_found ->
      Queue.add v q;
      log 3 "Adding binding : %s -> %a" Expr.(v.var_name) print v;
      add Expr.(v.var_name) v map
  in
  let map' = List.fold_left add_var map l in
  List.rev (Queue.fold (fun acc x -> x :: acc) [] q), map'

let new_name pre =
  let i = ref 0 in
  (fun () -> incr i; pre ^ (string_of_int !i))

let new_ty_name = new_name "ty#"
let new_term_name = new_name "term#"

let add_type_vars ~goalness env l =
  let l', map = add_vars Expr.debug_var_ttype env.type_vars l
      (fun Expr.Type -> Expr.ttype_var (new_ty_name ()))
      (fun name v map -> M.add name (Expr.type_var ~goalness v) map)
  in
  l', { env with type_vars = map }

let add_type_var ~goalness env v = match add_type_vars ~goalness env [v] with | [v'], env' -> v', env' | _ -> assert false

let add_term_vars ~goalness env l =
  let l', map = add_vars Expr.debug_var_ty env.term_vars l
      (fun ty -> Expr.ty_var (new_term_name ()) ty)
      (fun name v map -> M.add name (Expr.term_var ~goalness v) map)
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
    Expr.ttype_var s
  | _ -> raise Typing_error

let rec parse_ty ~goalness env = function
  | { Ast.term = Ast.Var s} -> find_type_var env s
  | { Ast.term = Ast.Const (Ast.String c)} -> Expr.type_app ~goalness (find_ty_cstr c) []
  | { Ast.term = Ast.App ({Ast.term = Ast.Const (Ast.String c) }, l) } ->
    let l' = List.map (parse_ty ~goalness env) l in
    Expr.type_app ~goalness (find_ty_cstr c) l'
  | t ->
    log 5 "Expected a type, but received : %a" Ast.debug_term t;
    raise Typing_error

let rec parse_sig ~goalness env = function
  | { Ast.term = Ast.Binding (Ast.AllTy, vars, t) } ->
    let typed_vars = List.map parse_ttype_var vars in
    let typed_vars, env' = add_type_vars ~goalness env typed_vars in
    let params, args, ret = parse_sig ~goalness env' t in
    (typed_vars @ params, args, ret)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, ret :: args) } ->
    [], List.map (parse_ty ~goalness env) args, parse_ty ~goalness env ret
  | t -> [], [], parse_ty ~goalness env t

let parse_ty_var ~goalness env = function
  | { Ast.term = Ast.Var s } ->
    Expr.ty_var s Builtin.type_i
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s }, ty) } ->
    Expr.ty_var s (parse_ty ~goalness env ty)
  | t ->
    log 5 "Expected a (typed) variable, received : %a" Ast.debug_term t;
    raise Typing_error

let default_cst_ty n ret = (Util.times n (fun () -> Builtin.type_i), ret)

let parse_let_var eval = function
  | { Ast.term = Ast.Column ({ Ast.term = Ast.Var s}, t) } -> (s, eval t)
  | _ -> raise Typing_error

let rec parse_term ~goalness ret env = function
  | { Ast.term = Ast.Var s } -> find_term_var env s
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) }
  | { Ast.term = Ast.Const Ast.String s } ->
    begin try
        find_term_var env s
      with Scoping_error _ ->
        Expr.term_app ~goalness (find_cst (default_cst_ty 0 ret) s) [] []
    end
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, l) } ->
    let f = find_cst (default_cst_ty (List.length l) ret) s in
    let n_ty_args = List.length (Expr.(f.var_type.fun_vars)) in
    let n_t_args = List.length (Expr.(f.var_type.fun_args)) in
    if List.length l <> n_ty_args + n_t_args then
      raise (Bad_arity (s, n_ty_args + n_t_args, l));
    let ty_args, t_args = Util.list_split_at n_ty_args l in
    Expr.term_app ~goalness f
      (List.map (parse_ty ~goalness env) ty_args)
      (List.map (parse_term ~goalness Builtin.type_i env) t_args)
  | { Ast.term = Ast.Binding (Ast.Let, vars, f) } ->
    let env' = List.fold_left (fun acc var ->
        let (s, t) = parse_let_var (parse_term ~goalness Builtin.type_i env) var in
        add_let_term acc s t) env vars
    in
    parse_term ~goalness ret env' f
  | t ->
    log 5 "Expected a term, received : %a" Ast.debug_term t;
    raise Typing_error

let rec parse_quant_vars ~goalness env = function
  | [] -> [], [], env
  | (v :: r) as l ->
    try
      let ttype_var = parse_ttype_var v in
      let ttype_var, env' = add_type_var ~goalness env ttype_var in
      let l, l', env'' = parse_quant_vars ~goalness env' r in
      ttype_var :: l, l', env''
    with Typing_error ->
      let l' = List.map (parse_ty_var ~goalness env) l in
      let l'', env' = add_term_vars ~goalness env l' in
      [], l'', env'

let rec parse_formula ~goalness env = function
  (* Formulas *)
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.True }, []) }
  | { Ast.term = Ast.Const Ast.True } -> Expr.f_true
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.False }, []) }
  | { Ast.term = Ast.Const Ast.False } -> Expr.f_false
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.And}, l) } ->
    Expr.f_and (List.map (parse_formula ~goalness env) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Or}, l) } ->
    Expr.f_or (List.map (parse_formula ~goalness env) l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Xor}, l) } ->
    assert false
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Imply}, l) } ->
    begin match l with
      | [p; q] -> Expr.f_imply (parse_formula ~goalness env p) (parse_formula ~goalness env q)
      | _ -> raise (Bad_arity ("=>", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Equiv}, l) } ->
    begin match l with
      | [p; q] -> Expr.f_equiv (parse_formula ~goalness env p) (parse_formula ~goalness env q)
      | _ -> raise (Bad_arity ("<=>", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Not}, l) } ->
    begin match l with
      | [p] -> Expr.f_not (parse_formula ~goalness env p)
      | _ -> raise (Bad_arity ("not", 1, l))
    end
  (* Binders *)
  | { Ast.term = Ast.Binding (Ast.All, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars ~goalness env vars in
    Expr.f_allty ttype_vars (Expr.f_all ty_vars (parse_formula ~goalness env' f))
  | { Ast.term = Ast.Binding (Ast.Ex, vars, f) } ->
    let ttype_vars, ty_vars, env' = parse_quant_vars ~goalness env vars in
    Expr.f_exty ttype_vars (Expr.f_ex ty_vars (parse_formula ~goalness env' f))
  | { Ast.term = Ast.Binding (Ast.Let, vars, f) } ->
    let env' = List.fold_left (fun acc var ->
        try
          let (s, t) = parse_let_var (parse_term ~goalness Builtin.type_i env) var in
          log 2 "Let-binding : %s -> %a" s Expr.debug_term t;
          add_let_term acc s t
        with Typing_error ->
          begin try
              let (s, f) = parse_let_var (parse_formula ~goalness env) var in
              log 2 "Let-binding : %s -> %a" s Expr.debug_formula f;
              add_let_prop acc s f
            with Typing_error ->
              assert false
          end) env vars
    in
    parse_formula ~goalness env' f
  (* (Dis)Equality *)
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Eq}, l) } ->
    begin match l with
      | [a; b] -> Expr.f_equal (parse_term ~goalness Builtin.type_i env a) (parse_term ~goalness Builtin.type_i env b)
      | _ -> raise (Bad_arity ("=", 2, l))
    end
  | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Distinct}, args) } ->
    let l = Util.list_diagonal (List.map (parse_term ~goalness Builtin.type_i env) args) in
    Expr.f_and (List.map (fun (a, b) -> Expr.f_not (Expr.f_equal a b)) l)
  (* Possibly bound variables *)
  | { Ast.term = Ast.App ({ Ast.term = Ast.Const Ast.String s }, []) }
  | { Ast.term = Ast.Const Ast.String s } | { Ast.term = Ast.Var s } as t ->
    begin try find_prop_var env s
      with Scoping_error _ -> Expr.f_pred (parse_term ~goalness Expr.type_prop env t) end
  (* Generic terms *)
  | { Ast.term = Ast.App _ }
  | { Ast.term = Ast.Const _ } as t ->
    Expr.f_pred (parse_term ~goalness Expr.type_prop env t)
  (* Absurd case *)
  | t ->
    log 0 "Expected a formula, received : %a" Ast.debug_term t;
    raise Typing_error

(* Exported functions *)
(* ************************************************************************ *)

let new_type_def (sym, n) =
  match sym with
  | Ast.String s -> add_type s (Expr.type_const s n)
  | _ ->
    log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let new_const_def (sym, t) =
  match sym with
  | Ast.String s ->
    let params, args, ret = parse_sig ~goalness:Expr.hypothesis empty_env t in
    add_cst s (Expr.term_const s params args ret)
  | _ ->
    log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let parse t =
  let f = parse_formula ~goalness:Expr.goal empty_env t in
  log 1 "New expr : %a" Expr.debug_formula f;
  f

