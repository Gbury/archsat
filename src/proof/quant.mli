
(** Base Tactics for reasoning on quantified formulas

    This module defines some helpers to deal with quantified
    formulas in proofs. *)

open Proof

(** {2 Prelude} *)

val epsilon_prelude : Prelude.t
(** Require the epsilon logic module. *)


(** {2 Constants} *)

val inhabited : Term.id
val inhabited_term : Term.t
(** Inhabitation type constructor *)

val inhabits : Term.id
val inhabits_term : Term.t
(** Inhabitation term constructor *)

val epsilon : Term.id
val epsilon_term : Term.t
(** Epsilon constructors. *)


(** {2 Term manipulation} *)

val match_ex : Term.t -> (Term.id * Term.t) option
(** Match an existencial. *)

val match_all : Term.t -> (Term.id * Term.t) option
(** Match an universally quantified formula. *)


(** {2 Instanciating} *)

val inst_not_ex : Term.t -> Term.t list -> Term.t
(** Given a term [t] of type [~ exists l, body], and a list of arguments [args],
    [inst_not_ex f args], returns a term where the quantified variables in [l]
    have been instantiated with the terms from [args]. *)

val inst_epsilon : Term.t -> (Term.t * Term.t) list -> Term.t
(** Given a term [t] of type [exists l, body], and a list of arguments
    of the form [epsilon, witness] where epsilon is an espilon term,
    and witness a term of the quantified type, returns *)

