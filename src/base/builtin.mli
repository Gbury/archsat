
(** Builtins Expr-related functions *)

(** {2 Builtin symbols} *)

type Expr.builtin += Cast

(** {2 Typing} *)

val type_i : Expr.ty
val i_cstr : Expr.ttype Expr.function_descr Expr.id
(** Equivalent of Tptp's '$i' *)

val cast_cstr : Expr.ty Expr.function_descr Expr.id
val cast : Expr.term -> Expr.ty -> Expr.term
(** Returns a 'casted' expression with the given type. *)

(** {2 Tuples} *)

val tuple : Expr.term list -> Expr.term

(** {2 Propositional calculus} *)

val p_true : Expr.term
val p_false : Expr.term
(** Terms constants for the 'true' and 'false' propositions. *)

val mk_prop : int -> Expr.formula
(** Generates a formula based on the given integer.
    The generated formula is a constant of type Expr.type_prop *)

(** {2 Absolute constants} *)

val const : Expr.ty -> Expr.term
(** Returns a constant with the given type. For equal types, equal constants
    will be returned. *)

