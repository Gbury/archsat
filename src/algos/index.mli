
(** Index on terms for fast unification.
    This module implements indexing on terms in order
    to have fast access to unifiable terms stored in the index.
    TODO: add link to fingerprinting index article. *)

(** {2 Naive Index} *)

module Simple(T: Set.OrderedType) : sig

  type t
  (** The type of indexes. The goal of an index is to allow
      eficient matching on big sets of terms. *)

  val empty : Util.Section.t -> t
  (** Create a new empty index. *)

  val add : Expr.term -> T.t -> t -> t
  (** Add a term with a payload to the index. *)

  val remove : Expr.term -> T.t -> t -> t
  (** Remove a term (and its payload) from the index. *)

  val find_unify : Expr.term -> t -> (Expr.term * Unif.t * T.t list) list
  (** Find all terms (and payloads) in the index that unify with a given pattern. *)

  val find_match : Expr.term -> t -> (Expr.term * Unif.t * T.t list) list
  (** Find all terms (and payloads) in the index that match a given pattern. *)

end
(** {2 Fingerprinting Index} *)

module Make(T: Set.OrderedType) : sig

  type t
  (** The type of indexes. The goal of an index is to allow
      eficient matching on big sets of terms. *)

  val empty : ?key:int list list -> Util.Section.t -> t
  (** Create a new empty index. *)

  val add : Expr.term -> T.t -> t -> t
  (** Add a term with a payload to the index. *)

  val remove : Expr.term -> T.t -> t -> t
  (** Remove a term (and its payload) from the index. *)

  val find_unify : Expr.term -> t -> (Expr.term * Unif.t * T.t list) list
  (** Find all terms (and payloads) in the index that unify with a given pattern. *)

  val find_match : Expr.term -> t -> (Expr.term * Unif.t * T.t list) list
  (** Find all terms (and payloads) in the index that match a given pattern. *)

end
