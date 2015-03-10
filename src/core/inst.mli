
val quant_compare : Expr.formula -> Expr.formula -> int option
(** Partial order representing the sub-formula inclusion on quantified
    formulas. *)

val quant_comparable : Expr.formula -> Expr.formula -> bool
(** Returns if the two given formulas are comparable according to compare_quant. *)

val split : Unif.t -> Unif.t list
(** Splits an arbitray unifier into a list. Each unifiers u in the list
    is such that in the set of formulas that generated the metas in u, all formula
    are comparable according to compare_quant.
    Additionally, no formula generating metas from two different unifiers in the list
    are comparable. *)

val simplify : Unif.t -> Unif.t
(** TODO *)

val soft_push : Unif.t -> unit
val hard_push : Unif.t -> unit
(** Takes an unifier and instanciates the given unifier, i.e pushed clauses to the sat solver
    that realizes the unifier. *)

