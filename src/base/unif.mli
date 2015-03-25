
(** Unification for terms *)

exception Not_unifiable_ty of Expr.ty * Expr.ty
exception Not_unifiable_term of Expr.term * Expr.term

(** {2 Unifiers} *)

type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}

val empty : t

val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool

val get_ty : t -> Expr.ttype Expr.meta -> Expr.ty
val get_term : t -> Expr.ty Expr.meta -> Expr.term

val get_ty_opt : t -> Expr.ttype Expr.meta -> Expr.ty option
val get_term_opt : t -> Expr.ty Expr.meta -> Expr.term option

val mem_ty : t -> Expr.ttype Expr.meta -> bool
val mem_term : t -> Expr.ty Expr.meta -> bool

val bind_ty : t -> Expr.ttype Expr.meta -> Expr.ty -> t
val bind_term : t -> Expr.ty Expr.meta -> Expr.term -> t

val follow_ty : t -> Expr.ty -> Expr.ty
val follow_term : t -> Expr.term -> Expr.term

val merge : t -> t -> t

(** {2 Meta protection} *)

val protect_inst : t -> t
val protect_ty : Expr.ty -> Expr.ty
val protect_term : Expr.term -> Expr.term

(** {2 Robinson unification} *)

val occurs_check_ty : t -> Expr.ty -> Expr.ty -> bool
val occurs_check_term : t -> Expr.term -> Expr.term -> bool

val robinson_ty : t -> Expr.ty -> Expr.ty -> t
val robinson_term : t -> Expr.term -> Expr.term -> t

val unify_ty : Expr.ty -> Expr.ty -> t
val unify_term : Expr.term -> Expr.term -> t

val cached_unify : Expr.term -> Expr.term -> t

