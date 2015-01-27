
let log_section = Util.Section.make "builtin"
let log i fmt = Util.debug ~section:log_section i fmt

(* Typing *)
(* ************************************************************************ *)

let i_cstr = Expr.type_const "$i" 0
let type_i = Expr.type_app i_cstr []

(* Tuples *)
(* ************************************************************************ *)

let tuple_ty_cstr n =
    let name = string_of_int n ^ "-tuple" in
    Expr.type_const name n

let tuple_cstr n =
    let name = string_of_int n ^ "-tuple" in
    let range = Util.list_range 1 (n + 1) in
    let vars = List.map (fun i -> Expr.ttype_var ("tuple#" ^ string_of_int i)) range in
    let ty_args = List.map Expr.type_var vars in
    let ret = Expr.type_app (tuple_ty_cstr n) ty_args in
    Expr.term_const name vars ty_args ret

let tuple l =
    let n = List.length l in
    let ty_l = List.map (fun t -> Expr.(t.t_type)) l in
    let f = tuple_cstr n in
    Expr.term_app f ty_l l

(* Propositional calculus *)
(* ************************************************************************ *)

let p_true = Expr.term_app (Expr.term_const "true" [] [] Expr.type_prop) [] []
let p_false = Expr.term_app (Expr.term_const "false" [] [] Expr.type_prop) [] []


let mk_prop i =
  let aux i =
    let c = Expr.term_const ("p" ^ string_of_int i) [] [] Expr.type_prop in
    Expr.f_pred (Expr.term_app c [] [])
  in
  if i >= 0 then
    aux i
  else
    Expr.f_not (aux ~-i)


