
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
exception Bad_arity of string
exception Scoping_error of string

(* Environment *)
(* ************************************************************************ *)

(* Hashtable from symbol name to type constructors *)
let types = H.create stack
(* Hashtable from symbol name to function symbols *)
let constants = H.create stack

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

type env = {
    type_vars : Expr.ttype Expr.var M.t;
    term_vars : Expr.ty Expr.var M.t;
}

let empty_env = {
    type_vars = M.empty;
    term_vars = M.empty;
}

let add_vars new_var map l =
  let q = Queue.create () in
  let add_var map v =
    try
      if M.mem Expr.(v.var_name) map then begin
        let v' = new_var Expr.(v.var_type) in
        Queue.add v' q;
        M.add Expr.(v.var_name) v' map
      end else
        raise Not_found
    with Not_found ->
      Queue.add v q;
      M.add Expr.(v.var_name) v map
  in
  let map' = List.fold_left add_var map l in
  List.rev (Queue.fold (fun acc x -> x :: acc) [] q), map'

let new_name =
    let i = ref 0 in
    (fun () -> incr i; "#" ^ (string_of_int !i))

let add_type_vars env l =
    let l', map = add_vars (fun _ -> Expr.ttype_var (new_name ())) env.type_vars l in
    l', { env with type_vars = map }

let add_term_vars env l =
    let l', map = add_vars (fun ty -> Expr.ty_var (new_name ()) ty) env.term_vars l in
    l', { env with term_vars = map }

let find_var map s =
    try
        M.find s map
    with Not_found ->
        raise (Scoping_error s)

let find_type_var env s = find_var env.type_vars s
let find_term_var env s = find_var env.term_vars s

(* Term parsing *)
(* ************************************************************************ *)

let parse_ttype_var = function
    | { Ast.term = Ast.Var s } -> Expr.ttype_var s
    | _ -> raise Typing_error

let rec parse_ty env = function
    | { Ast.term = Ast.Var s} -> Expr.type_var (find_type_var env s)
    | { Ast.term = Ast.Const (Ast.String c)} -> Expr.type_app (find_ty_cstr c) []
    | { Ast.term = Ast.App ({Ast.term = Ast.Const (Ast.String c) }, l) } ->
      let l' = List.map (parse_ty env) l in
      Expr.type_app (find_ty_cstr c) l'
    | t ->
      log 0 "Expected a type, but received : %a" Ast.debug_term t;
      raise Typing_error

let rec parse_sig env = function
    | { Ast.term = Ast.Binding (Ast.AllTy, vars, t) } ->
            let typed_vars = List.map parse_ttype_var vars in
            let typed_vars, env' = add_type_vars env typed_vars in
            let params, args, ret = parse_sig env' t in
            (typed_vars @ params, args, ret)
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, ret :: args) } ->
            [], List.map (parse_ty env) args, parse_ty env ret
    | _ -> assert false

let rec parse_term env t = assert false

let rec parse_formula env = function
    (* Formulas *)
    | { Ast.term = Ast.Const Ast.True } -> Expr.f_true
    | { Ast.term = Ast.Const Ast.False } -> Expr.f_false
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.And}, l) } ->
      Expr.f_and (List.map (parse_formula env) l)
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Or}, l) } ->
      Expr.f_or (List.map (parse_formula env) l)
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Xor}, l) } ->
      assert false
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Imply}, l) } ->
      begin match l with
        | [p; q] -> Expr.f_imply (parse_formula env p) (parse_formula env q)
        | _ -> raise (Bad_arity "=>")
      end
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Equiv}, l) } ->
      begin match l with
        | [p; q] -> Expr.f_equiv (parse_formula env p) (parse_formula env q)
        | _ -> raise (Bad_arity "<=>")
      end
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Not}, l) } ->
      begin match l with
        | [p] -> Expr.f_not (parse_formula env p)
        | _ -> raise (Bad_arity "not")
      end
    (* Quantifications *)
    (* Terms *)
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Eq}, l) } ->
      begin match l with
        | [a; b] -> Expr.f_equal (parse_term env a) (parse_term env b)
        | _ -> raise (Bad_arity "=")
      end
    | { Ast.term = Ast.App _ } as t -> Expr.f_pred (parse_term env t)
    (* Absurd case *)
    | t ->
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
      let params, args, ret = parse_sig empty_env t in
      let c = Expr.term_const s params args ret in
      log 1 "New constant : %a" Expr.debug_const_ty c;
      H.add constants s c
    | _ ->
      log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let parse t =
    log 1 "Parsing expr (TODO).";
    Expr.f_true

