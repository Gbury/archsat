
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

let add_var map v = M.add Expr.(v.var_name) v map
let add_vars map l = List.fold_left add_var map l

let find_var map s =
    try
        M.find s map
    with Not_found ->
        raise (Scoping_error s)

(* Term parsing *)
(* ************************************************************************ *)

let parse_ttype_var = function
    | { Ast.term = Ast.Var s } -> Expr.ttype_var s
    | _ -> raise Typing_error

let rec parse_ty map = function
    | { Ast.term = Ast.Var s} -> Expr.type_var (find_var map s)
    | { Ast.term = Ast.Const (Ast.String c)} -> Expr.type_app (find_ty_cstr c) []
    | { Ast.term = Ast.App ({Ast.term = Ast.Const (Ast.String c) }, l) } ->
      let l' = List.map (parse_ty map) l in
      Expr.type_app (find_ty_cstr c) l'
    | t ->
      log 0 "Expected a type, but received : %a" Ast.debug_term t;
      raise Typing_error

let rec parse_sig map = function
    | { Ast.term = Ast.Binding (Ast.AllTy, vars, t) } ->
            let typed_vars = List.map parse_ttype_var vars in
            let map' = add_vars map typed_vars in
            let params, args, ret = parse_sig map' t in
            (typed_vars @ params, args, ret)
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, ret :: args) } ->
            [], List.map (parse_ty map) args, parse_ty map ret
    | _ -> assert false

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
      let params, args, ret = parse_sig M.empty t in
      let c = Expr.term_const s params args ret in
      log 1 "New constant : %a" Expr.debug_const_ty c;
      H.add constants s c
    | _ ->
      log 0 "Illicit type declaration for symbol : %a" Ast.debug_symbol sym

let parse t =
    log 1 "Parsing expr (TODO).";
    Expr.f_true

