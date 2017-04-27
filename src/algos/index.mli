
(** Index on terms for fast unification.
    This module implements indexing on terms in order
    to have fast access to unifiable terms stored in the index.
    TODO: add link to fingerprinting index article. *)

(** {2 Common signature} *)

module type S = sig

  type t
  (** The type of indexes. The goal of an index is to allow
      eficient matching on big sets of terms. *)

  type value
  (** The type of values stored in the index. *)

  val add : Expr.term -> value -> t -> t
  (** Add a term with a payload to the index. *)

  val remove : Expr.term -> value -> t -> t
  (** Remove a term (and its payload) from the index. *)

  val find_equal : Expr.term -> t -> (Expr.term * value list) list
  (** Find all terms (and payloads) in the index that are equal to a given pattern *)

  val find_unify : Expr.term -> t -> (Expr.term * Mapping.t * value list) list
  (** Find all terms (and payloads) in the index that unify with a given pattern. *)

  val find_match : Expr.term -> t -> (Expr.term * Mapping.t * value list) list
  (** Find all terms (and payloads) in the index that match a given pattern. *)

end

(** {2 Naive Index} *)

module Simple(T: Set.OrderedType) : sig

  include S with type value := T.t

  val empty : Section.t -> t
  (** Create a new empty index. *)

end
(** {2 Fingerprinting Index} *)

module Fingerprint : sig

  type t = Expr.ty Position.res
  (** The type of a fingerprint. *)

  val compare : t -> t -> int
  (** Compare two fingerprints. *)

  val print : Format.formatter -> t -> unit
  (** Print a fingerprint. *)

end

module Make(T: Set.OrderedType) : sig

  include S with type value := T.t

  val empty : ?key:int list list -> Section.t -> t
  (** Create a new empty index. *)

  val fingerprint : t -> Expr.term -> Fingerprint.t list
  (** Return the fingerprint of a term in an index. *)

end



