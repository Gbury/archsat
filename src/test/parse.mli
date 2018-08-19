(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Easy expr building

    This modules defines prefix and infx operators to help manually
    build expressions. here are a fex exmaples of what one can do with this
    module:
    {[
      let eq = Parse.(f_a @ [ ~~ a_0 ] === type_a#:0);;
      val eq : Expr.formula = ⟦f_a(a_0) = m0_m0⟧
    ]}
*)


(** {2 Base constants} *)

include module type of Expr_test.C


(** {2 Type construction} *)

val (!%) : Expr.ttype Expr.id -> Expr.ty
(** Prefix operator to turn a variable symbol into a type. *)

val (!~) : Expr.Id.TyCstr.t -> Expr.ty
(** Prefix operator to turn a constant symbol (wiht no arguments) int a type *)

val (@@) : Expr.Id.TyCstr.t -> Expr.ty list -> Expr.ty
(** Infix operator for application of type constructors *)


(** {2 Term construction} *)

val (~%) : Expr.ty Expr.id -> Expr.term
(** Prefix operator to turn a variable symbol into a term *)

val (#:) : Expr.ty -> int -> Expr.term
(** Infix operator to generate a meta from a type and an integer, and
    return the corresponding term. *)

val (~~) : Expr.Id.Const.t -> Expr.term
(** Prefix symbol to turn a constant symbol (with no arguments) into a term. *)

val (@) : Expr.Id.Const.t -> Expr.term list -> Expr.term
(** Infix operator for temr application (with no type arguments) *)


(** {2 Formula construction} *)

val (?^) : Expr.term -> Expr.formula
(** Prefix opertor for turning a term into a formula using {Expr.Formula.pred} *)

val (===) : Expr.term -> Expr.term -> Expr.formula
(** Infix operator to create equality formulas *)

val (&&) : Expr.formula -> Expr.formula -> Expr.formula
(** Infix operator for conjunction of formulas *)

val (||) : Expr.formula -> Expr.formula -> Expr.formula
(** Infix operator for disjunction of formulas *)

val (=>) : Expr.formula -> Expr.formula -> Expr.formula
(** Infix operator for implication *)

