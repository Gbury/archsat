
(** Unification between terms using unitary supperposisiton.
    This module uses unitary supperposition to derive potential unifiers. *)

type t
(** Persistent type for supperposisiton. *)

val empty : (Unif.t list -> unit) -> Util.Section.t -> t
(** Create an empty supperposisiton state. The function provided will
    be called on all unifiers found during solving. *)

val add_eq : t -> Expr.term -> Expr.term -> t
val add_neq : t -> Expr.term -> Expr.term -> t
(** Add an (in)equality to the state queue, i.e it does not do much. *)

val solve : t -> t
(** Solve the given system, saturating the state with the inferred
    equalities and inequalities. It is during this function call that
    the callback given when creating the state is called. *)

