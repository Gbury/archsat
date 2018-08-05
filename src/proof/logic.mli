
(** Base Tactics for logic.

    This module defines a good quantity of base tactics
    (i.e functions that operate on proof positions) related
    to propositional logic. *)

open Proof

(** {2 Convenience functions} *)

val extract_open : Proof.pos -> Proof.sequent
(** Extract the sequent from an open proof position. *)

(** {2 Preludes} *)

val classical : Prelude.t
(** The prelude requiring classical logic *)


(** {2 Some terms and matching functions} *)

val true_proof : Term.t
(** The term proving [true]. *)

val match_not : Term.t -> Term.t option
val match_or : Term.t -> (Term.t * Term.t) option
val match_and : Term.t -> (Term.t * Term.t) option
(** Some wrappers around {!Term.pmatch}. *)

(** {2 Simple tactics} *)

val find : Term.t -> (Term.t -> (pos, 'a) tactic) -> (pos, 'a) tactic
(** Wraps a tactic that expects a term. Finds the given term in the env,
    and give its id to the wrapped strategy. *)

val ctx : (Proof.sequent -> (pos, 'a) tactic) -> (pos, 'a) tactic
(** Wrapper around tactics to access environment (and use it to compute
    parameters for the tactic). *)

val fold : ('a -> (pos, pos) tactic) -> 'a list -> (pos, pos) tactic
(** Fold unary tactis over a list of arguments. *)

val ensure : (pos, bool) tactic -> (pos, unit) tactic
(** Ensures the bool-returning tactic succeeds in closing the proof. *)

val intro : ?post:(Term.t -> (pos, pos) tactic) -> string -> (pos, pos) tactic
val introN : ?post:(Term.t -> (pos, pos) tactic) -> string -> int -> (pos, pos) tactic
(** Introduction tactic. The string given is used as prefix
    for the name of the newly introduced hypothesis. *)

val cut :
  f:((pos, unit) tactic) ->
  string -> Term.t -> (pos, Term.id * pos) tactic
(** Cut/assert a given term (using the string as prefix for the env),
    and use the given function to prove the asserted term. *)

val exact  : Prelude.t list -> Term.t -> (pos, unit) tactic
val apply1 : Prelude.t list -> Term.t -> (pos, pos) tactic
val apply2 : Prelude.t list -> Term.t -> (pos, pos * pos) tactic
val apply3 : Prelude.t list -> Term.t -> (pos, pos * pos * pos) tactic
(** Fixed arity applications. *)

val split :
  left:((pos, unit) tactic) ->
  right:((pos, unit) tactic) ->
  (pos * pos, unit) tactic
(** Convenience operator for operating on a pair of positions. *)

val split3 :
  first:((pos, unit) tactic) ->
  second:((pos, unit) tactic) ->
  third:((pos, unit) tactic) ->
  (pos * pos * pos, unit) tactic
(** Convenience operators for mainpulating multiple positions at a time. *)


(** {2 Standard tactics} *)

val trivial : (pos, bool) tactic
(** Try and find the goal in the environment.
    Returns true if the branch has been closed, else returns false. *)

val exfalso : (pos, pos) tactic
(** Apply exfalso, if needed, in order to get a sequent of the form
    Gamm |- False. *)

val absurd : Term.t -> (pos, unit) tactic
(** Given a term [t], find [t] and its negation in the environment
    in order to close the branch, possibly applying exfalso if needed. *)

val or_elim :
  f:(Term.t -> (pos, unit) tactic) ->
  Term.t -> (pos, unit) tactic
(** Eliminate a disjunction present in the environment. *)

val and_intro :
  f:(Term.t -> (pos, unit) tactic) -> (pos, unit) tactic
(** Introduce a conjunction.
    TODO: some more doc. *)

val or_intro : Term.t -> (pos, pos) tactic
(** Introduce a dijunction.
    TODO: some more doc *)

val and_elim : Term.t -> (pos, pos) tactic
(** Eliminate a conjunction, introducing its individual terms in the env. *)

val not_not_elim : string -> Term.t -> (pos, pos) tactic
(** Given a goal of the form [False], and with [~ ~ t] in the env,
    introduce [t] in the environment. *)

val normalize : string -> Term.t -> (pos, pos) tactic
(** Try and apply doulbe negation elimination to introduce the given term,
    if it is not already present. *)

val not_not_intro : ?prefix:string -> (pos, pos) tactic
(** Given a goal of the form [~ ~ t], reduce it to [t],
    by doing an intro and then applying the newly introduced term. *)

(** {2 Classical tactics} *)

val nnpp : ?handle:(Term.id -> unit) -> (pos, pos) tactic
(** Applies nnpp *only if necessary*, to get at the end a
    pos to a sequent of the form Gamma |- False.
    The resulting proof may, or may *not* be classical. *)


(** {2 Weak clause translation} *)

val clause_type : Term.t list -> Term.t
(** Computes the weak clause encoding of the given list of terms,
    i.e. [~ l_1 -> ... -> ~ l_n -> False]. *)

val resolve_clause : Term.id -> Term.id -> Term.t list -> Term.t
(** Compute the resolution of two clauses. *)

val resolve : Term.id -> Term.id -> Term.t list -> (pos, Term.id * pos) tactic
(** Resolution of clauses *)

val remove_duplicates : Term.id -> Term.t list -> (pos, Term.id * pos) tactic
(** Resolution of clauses *)

