
(** Unification for terms *)

exception Not_unifiable_ty of Expr.ty * Expr.ty
exception Not_unifiable_term of Expr.term * Expr.term

(** {2 Unifiers} *)

type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}
(** The type of unifiers. Used to represent subsitutions
    on both types and terms. *)

val empty : t
(** The empty substitution. *)

val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
(** Standard functions on substitutions. *)

val get_ty : t -> Expr.ttype Expr.meta -> Expr.ty
val get_term : t -> Expr.ty Expr.meta -> Expr.term
(** Accessors.
    @raise Not_found if no binding is found. *)

val get_ty_opt : t -> Expr.ttype Expr.meta -> Expr.ty option
val get_term_opt : t -> Expr.ty Expr.meta -> Expr.term option
(** Wrappers for accessors. *)

val mem_ty : t -> Expr.ttype Expr.meta -> bool
val mem_term : t -> Expr.ty Expr.meta -> bool
(** Test for existence of bindings *)

val bind_ty : t -> Expr.ttype Expr.meta -> Expr.ty -> t
val bind_term : t -> Expr.ty Expr.meta -> Expr.term -> t
(** Add new bindings. *)

val follow_ty : t -> Expr.ty -> Expr.ty
val follow_term : t -> Expr.term -> Expr.term
(** Applies bindings in the substitution until either
    a non-meta variable if found, or the meta-variable is not in the substitution.
    Pseudo-code examples :
    [follow_term \[x, y; y, f(a)\] x = f(a)]
    [follow_term \[x; f(y); y, a] x = f(y)] *)

val merge : t -> t -> t
(** [merge s s'] adds all bindings of [s] to [s'] and returns the result.
    In particular bindings of [s] will override bindings of [s'] if there are collisions. *)

val inverse : t -> t
(** [inverse s] returns a substitution with the same bindings as [s] except
    for bindings of [s] which binds a meta-variable [m] to another meta-variable [m'],
    in which case, the substitution returned contains a binding from [m'] to [m]. *)

val fixpoint : t -> t
(** Computes the fixpoint of the substitution. May not terminate if the substitution
    contains cylces, i.e occurs_check should return false on all bindings of the substitution. *)

(** {2 Unification caching} *)

type 'a cache
(** The type of caches for binary functions on terms, with return type 'a.
    Currently implemented with a Hash table.
    Two pair of terms are equal iff there exists an involution
    of the meta-variables unifying the temrs, such that
    meta variables are only bound to meta-variables generated
    by the same formula. *)

val new_cache : unit -> 'a cache
(** Create a new cache. *)

val clear_cache : 'a cache -> unit
(** Empty the cache table. *)

val with_cache : 'a cache -> (Expr.term -> Expr.term -> 'a) ->
  Expr.term -> Expr.term -> 'a
(** Wraps the given function with the given cache. *)

(** {2 Robinson unification} *)

val unify_ty : Expr.ty -> Expr.ty -> t
val unify_term : Expr.term -> Expr.term -> t
(** Unification on types and terms. Currently uses robinson unification. *)

val occurs_check_ty : t -> Expr.ty -> Expr.ty -> bool
val occurs_check_term : t -> Expr.term -> Expr.term -> bool
(** Occurs check on terms and types. *)

val robinson_ty : t -> Expr.ty -> Expr.ty -> t
val robinson_term : t -> Expr.term -> Expr.term -> t
(** Robinson unification with input substitution. Can be used to extend substitutions. *)

