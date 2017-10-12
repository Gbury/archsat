
(** Builtin symbols

    This module defines usual symbols that are not
    part of the strict core of first-order terms.
*)

(** Standard tags for terms and formulas *)
module Tag : sig

  val rwrt : unit Tag.t
  (** This tag denotes formulas that are specified as
      rewrite rules in the source problem. *)

end

(** Misc symbols *)
module Misc : sig

  (** {5 Builtin symbols} *)

  type Expr.builtin +=
    | Cast    (** cast function *)
    | True    (** [true] as a term *)
    | False   (** [false] as a term *)
  (** New builtins symbols *)

  (** {5 Typing} *)

  val cast_cstr : Expr.Id.Const.t
  val cast : Expr.term -> Expr.ty -> Expr.term
  (** Returns a 'casted' expression with the given type. *)

  (** {5 Tuples} *)

  val tuple : Expr.term list -> Expr.term
  (** Create a tuple from a list of terms *)

  (** {5 Propositional calculus} *)

  val p_true : Expr.term
  val p_false : Expr.term
  (** Terms constants for the 'true' and 'false' propositions. *)

  val mk_prop : int -> Expr.formula
  (** Generates a formula based on the given integer.
      The generated formula is a constant of type Expr.type_prop *)

  (** {5 Absolute constants} *)

  val const : Expr.ty -> Expr.term
  (** Returns a constant with the given type. For equal types, equal constants
      will be returned. *)

end

(** Arithmetic builtins *)
module Arith : sig

  (** {5 Arithmetic builtins declarations} *)

  type ty = Int | Rat | Real

  type value = Int of Z.t | Rat of Q.t | Real of Q.t Lazy.t

  type op =
    | Less | Lesseq
    | Greater | Greatereq
    | Minus (* unary minus *)
    | Sum | Difference
    | Product | Quotient

  type Expr.builtin +=
    | Type of ty
    | Val of value
    | Op of op

  (** {5 Operations on builtins} *)

  val cmp_types : ty -> ty -> int

  val add : value -> value -> value
  val mul : value -> value -> value

  (** {5 Expressions for arithmetic types} *)

  val int_cstr : Expr.Id.TyCstr.t
  val rat_cstr : Expr.Id.TyCstr.t
  val real_cstr : Expr.Id.TyCstr.t

  val type_int : Expr.ty
  val type_rat : Expr.ty
  val type_real : Expr.ty

  (** {5 Arithmetic operators} *)

  type operator

  val less : operator
  val lesseq : operator
  val greater : operator
  val greatereq : operator

  val sum : operator
  val diff : operator
  val mult : operator
  val div : operator
  val uminus : operator

  val is_int : operator
  val is_rat : operator
  val is_real : operator

  val apply : operator -> Expr.term list -> Expr.term option

end
