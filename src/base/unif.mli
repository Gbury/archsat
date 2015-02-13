
(** Unification for terms *)

exception Not_unifiable_ty of Expr.ty * Expr.ty
exception Not_unifiable_term of Expr.term * Expr.term

val protect_term : Expr.term -> Expr.term

(** {2 Unifiers} *)

type t

val empty : t

val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool

val get_ty : t -> Expr.ttype Expr.meta -> Expr.ty
val get_term : t -> Expr.ty Expr.meta -> Expr.term

val bind_ty : t -> Expr.ttype Expr.meta -> Expr.ty -> t
val bind_term : t -> Expr.ty Expr.meta -> Expr.term -> t

(** {2 Robinson unification} *)

val unify_ty : Expr.ty -> Expr.ty -> t
val unify_term : Expr.term -> Expr.term -> t

val cached_unify : Expr.term -> Expr.term -> t

