
(** Positions insisde terms and types.
    This module provides tools to record positions
    inside terms as paths. *)

exception Invalid
(** Returned when a position is used in an expression, but the path
    representing the position does not exist. *)

module type S = sig
  (** Type signature for a module that implements
      positions inside an arbitrary type *)

  type t
  (** The type of paths/positions inside a value of type [expr]. *)
  type expr
  (** The type on values on which paths can be used. *)

  val root : t
  val arg : int -> t -> t
  (** Functions to build paths. *)

  val compare : t -> t -> int
  (** Comparison between paths *)

  val apply : t -> expr -> expr
  (** Returns the expression at a given position. *)

  val substitute : t -> by:expr -> expr -> expr
  (** [substitute p v t] returns [t] where the expression at posisiton [p]
      has been substituted with [v]. *)

  val fold : ('a -> t -> expr -> 'a) -> 'a -> expr -> 'a
  (** Fold on all sub-expressions of an expression. *)

  val find_map : (t -> expr -> 'a option) -> expr -> 'a option
  (** Fold on al subterms but stop on the first time a not [None] result is returned. *)

end

module Ty : sig
  include S with type expr = Expr.ty
end

module Term : sig
  include S with type expr = Expr.term
end
