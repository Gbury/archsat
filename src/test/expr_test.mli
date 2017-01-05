
(** Random Expressions

    This module defines some random generators for expressions.
    These are intended for use in qcheck tests.
*)

(** {2 Type definition} *)

type 'a gen = 'a QCheck.Gen.t
type 'a sized = 'a QCheck.Gen.sized
type 'a shrink = 'a QCheck.Shrink.t
type 'a arbitrary = 'a QCheck.arbitrary
(** Some type abbreviations *)

(** {2 Common interface} *)

module type S = sig

  type t

  val print : t -> string
  (** Print types to string. *)

  val small : t -> int
  (** Returns the size of a type. *)

  val shrink : t shrink
  (** Shrink a type by trying all its subtypes. *)

  val sized : t sized
  (** A sized generator for types. *)

  val gen : t gen
  (** Generate a random type. *)

  val t : t arbitrary
  (** Arbitrary for types. To use in qcheck tests. *)

  val make : t gen -> t arbitrary
  (** Convenient shortcut. *)

end

(** {2 Types} *)

module Ty : sig

  include S with type t := Expr.ty

end

(** {2 Terms} *)

module Term : sig

  include S with type t := Expr.term

  type config = {
    var : int;
    meta: int;
  }

  val typed : config:config -> Expr.ty -> Expr.term sized
  (** Generate a term with the given size and type.
      @param ground if false then variables can appear in the generatd term.
        (default [true]) *)

end

(** {2 Formulas} *)

module Formula : sig

  include S with type t := Expr.formula

  type config = {
    term  : Term.config;
    eq    : int;
    pred  : int;
    neg   : int;
    conj  : int;
    disj  : int;
    impl  : int;
    equiv : int;
    all   : int;
    allty : int;
    ex    : int;
    exty  : int;
  }

  val eq : config:config -> Expr.formula sized
  val pred : config:config -> Expr.formula sized
  (** Individual generator for expressions. *)

  val guided : config:config -> Expr.formula sized
  (** Generate a formula using a given configuration. *)

  val closed : config:config -> Expr.formula sized
  (** Generate a closed formula. *)

  val meta : Expr.formula -> Expr.formula
  (** Replaces variable with meta-variables in the formulas of a generator. *)

  val meta_tt : (Expr.term * Expr.term) -> (Expr.term * Expr.term)
  (** Takes a pair of terms with free variables and substitute them with
      meta-variables. *)

end

(** {2 Substitutions} *)

module Subst : sig

  type t = (Expr.ty Expr.meta, Expr.term) Expr.Subst.t
  (** Type alias for the substitutions. *)

  include S with type t := t

end

