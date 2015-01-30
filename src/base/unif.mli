
(** Unification for terms *)

exception Not_unifiable

(** {2 Module for unifiers} *)

module S : sig
  type t

  val empty : t
  val bind : Expr.ty Expr.meta -> Expr.term -> t -> t

  val hash : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool

  val bindings : t -> (Expr.ty Expr.meta * Expr.term) list
end

(** {2 Robinson unification} *)

val unify_simple : Expr.term -> Expr.term -> S.t
val cached_unify : Expr.term -> Expr.term -> S.t

