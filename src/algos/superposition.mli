
(** Unification between terms using unitary supperposisiton.
    This module uses unitary supperposition to derive potential unifiers. *)

type t
(** Persistent type for supperposisiton. *)

type rules = {
  er : bool;
  sn : bool;
  sp : bool;
  es : bool;
  rp : bool;
  rn : bool;
}
(** The type of configuration for superposition.
    Each bool indicates wether the corresponding rule should be used. *)

val empty : ?rules:rules -> Section.t -> (Mapping.t -> unit) -> t
(** Create an empty supperposisiton state. The function provided will
    be called on all unifiers found during solving.
    @param rules Specify what rules to use during saturation.
      By default all rules are used.
*)

val add_eq : t -> Expr.term -> Expr.term -> t
val add_neq : t -> Expr.term -> Expr.term -> t
(** Add an (in)equality to the state queue, i.e it does not do much. *)

val solve : t -> t
(** Solve the given system, saturating the state with the inferred
    equalities and inequalities. It is during this function call that
    the callback given when creating the state is called. *)

