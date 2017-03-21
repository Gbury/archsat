
(** Easy construction of expressions

    This module defines infix notations to facilitate the manual
    cration of expressions.
*)

include Expr_test.C

(* Type creation *)
(* ************************************************************************ *)

let (!%) c = Expr.Ty.of_id c
let (!~) c = Expr.Ty.apply c []
let (@@) f args = Expr.Ty.apply f args

(* Term creation *)
(* ************************************************************************ *)

let (~%) c = Expr.Term.of_id c
let (~~) c = Expr.Term.apply c [] []
let (@) f args = Expr.Term.apply f [] args

let (#:) ty n =
  Expr.Term.of_meta ((Expr_test.Meta.get ty).(n))

(* Formula creation *)
(* ************************************************************************ *)

let (===) = Expr.Formula.eq
let (?^) = Expr.Formula.pred

let (&&) a b = Expr.Formula.f_and [a; b]
let (||) a b = Expr.Formula.f_or [a; b]
let (=>) a b = Expr.Formula.imply a b

