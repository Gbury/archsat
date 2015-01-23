
(* Typing *)
(* ************************************************************************ *)

let type_i = Expr.type_app (Expr.type_const "$i" 0) []

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


