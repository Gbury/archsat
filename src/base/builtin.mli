
(** Builtins Expr-related functions *)

(** {2 Typing} *)

val type_i : Expr.ty
val i_cstr : Expr.ttype Expr.function_descr Expr.var
(** Equivalent of Tptp's '$i' *)

(** {2 Propositional calculus} *)

val p_true : Expr.term
val p_false : Expr.term
(** Terms constants for the 'true' and 'false' propositions. *)

val mk_prop : int -> Expr.formula
(** Generates a formula based on the given integer.
    The generated formula is a constant of type Expr.type_prop *)


