
(** Base Tactics for equality reasoning

    This module defines a good quantity of base tactics
    (i.e functions that operate on proof positions)
    related to handling equalities and uninterpreted functions. *)

open Proof

(** {2 Simple tactics} *)

val refl : (pos, unit) tactic
(** Allows t prove goals that are of the form [x = x]. *)

val trans : (Term.t * Term.t) list -> (pos, unit) tactic
(** Prove an equality using transitivity with the chains of equalities
    given as argument. *)

val replace : eq:((pos, unit) tactic) -> by:Term.t -> Term.t -> (pos, pos) tactic
(** [replace ~eq ~by:u t] is a tactic that, in the current goal, replace
    [t] by [u], using the [eq] tactic to prove the equality [t = u]. *)

val subst :
  eq:((pos, unit) tactic) -> by:Term.t ->
  Position.t -> Term.t -> (pos, pos) tactic
(** More low-level version of replace. Given the position and the goal
    (allows to avoid normalisation of the goal). *)

val congruence_term : Term.t -> (Term.t * Term.t) list -> (pos, unit) tactic
(** Prove an equality [f x1 ... xn = f y1 .. yn] given that
    [x1 = y1], ... [xn = yn] are in the hypotheses.*)

val congruence_prop : Term.t -> (Term.t * Term.t) list -> (pos, unit) tactic
(** Prove [f x1 ... xn], given that [f y1 .. yn],
    [x1 = y1], ... [xn = yn] are in the hypotheses.*)

