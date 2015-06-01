
module Misc : sig

  (** {5 Builtin symbols} *)

  type Expr.builtin += Cast

  (** {5 Typing} *)

  val cast_cstr : Expr.ty Expr.function_descr Expr.id
  val cast : Expr.term -> Expr.ty -> Expr.term
  (** Returns a 'casted' expression with the given type. *)

  (** {5 Tuples} *)

  val tuple : Expr.term list -> Expr.term

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

module Arith : sig

  type ty = Int | Rat | Real

  type value = Int of Z.t | Rat of Q.t | Real of Q.t

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

  (** {5 Operations on builtins *)
  val cmp_types : ty -> ty -> int

  val add : value -> value -> value
  val mul : value -> value -> value

  (** {5 Expressions for arithmetic types} *)

  val int_cstr : Expr.ttype Expr.function_descr Expr.id
  val rat_cstr : Expr.ttype Expr.function_descr Expr.id
  val real_cstr : Expr.ttype Expr.function_descr Expr.id

  val type_int : Expr.ty
  val type_rat : Expr.ty
  val type_real : Expr.ty

  (** {5 Arithmetic operators} *)

  type operator = ty -> Expr.ty Expr.function_descr Expr.id

  val apply : operator -> Expr.term list -> Expr.term option

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

end
