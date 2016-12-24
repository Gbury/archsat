
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

end

(** {2 Types} *)

module Ty : sig

  include S with type t := Expr.ty

end

(** {2 Terms} *)

module Term : sig

  include S with type t := Expr.term

  val typed : ?ground:bool -> Expr.ty -> Expr.term sized
  (** Generate a term with the given size and type.
      @param ground if false then variables can appear in the generatd term.
        (default [true]) *)

end

(** {2 Formulas} *)

module Formula : sig

  include S with type t := Expr.formula

  val eq : ?ground:bool -> Expr.formula sized
  val pred : ?ground:bool -> Expr.formula sized
  (** Individual generator for expressions. *)

  val meta : Expr.formula sized -> Expr.formula sized
  (** Replaces variable with meta-variables in the formulas of a generator. *)

end

