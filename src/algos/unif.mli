
(** Unification for expressions *)

(** {2 Unifiers} *)

type t = {
  ty_map : (Expr.ttype Expr.meta, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.meta, Expr.term) Expr.Subst.t;
}
(** The type of unifiers. Used to represent subsitutions
    from meta-variables to types or terms. *)

val empty : t
(** The empty substitution. *)
val is_empty : t -> bool
(** Test if the substitution is empty *)

val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
(** Standard functions on substitutions. *)

val print : Format.formatter -> t -> unit
(** Printing function for substitutions. *)

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
    {ul
      {li [follow_term \[x -> y; y -> f(a)\] x = f(a)]}
      {li [follow_term \[x -> f(y); y -> a\] x = f(y)]}
    } *)

val inverse : t -> t
(** [inverse s] returns a substitution with the same bindings as [s] except
    for bindings of [s] which binds a meta-variable [m] to another meta-variable [m'],
    in which case, the substitution returned contains a binding from [m'] to [m] instead. *)

val type_subst : t -> Expr.ty -> Expr.ty
val term_subst : t -> Expr.term -> Expr.term
(** Subsitutions of meta-variables, given a unifier. May not terminate if the substitution
    contains cycles. *)

val occurs_ty : t -> Expr.ttype Expr.meta list -> Expr.ty -> bool
val occurs_term : t -> Expr.ty Expr.meta list -> Expr.term -> bool
(** Occurs check on terms and types, expected return result should be false
    (i.e no cycles detected). *)

val occurs_check : t -> bool
(** Returns true if no bindings of the substitution violates the usual occurs check criterion
    (used for instance in Robinson unifiction). *)

val fixpoint : t -> t
(** Computes the fixpoint of the substitution. May not terminate if the substitution
    contains cylces. Consequently, occurs_check should return true on any subsitution
    used with this function. *)

val merge : t -> t -> t option
(** Try and merge two substitutions.
    TODO: document more this funciton, :p *)

val to_formula : t -> Expr.formula
(** Generate a conjunction of all bindings of the substitution as equalities *)

(** {2 Unification caching} *)

module Cache : sig

  type 'a t
  (** The type of caches for binary functions on terms, with return type 'a.
      Currently implemented with a Hash table.
      Two pair of terms [(s, t)] and [(s', t')] are equal iff there exists
      an involution of the meta-variables [u], such that:
      {ul
      {li [u] unifies [s] with [s'] and [t] with [t']}
      {li Any binding in [u] that links a meta [m] to a meta [m']
          verifies that [m] and [m'] are defined by the same formula.}
      }
  *)

  val create : unit -> 'a t
  (** Create a new cache. *)

  val clear : 'a t -> unit
  (** Empty the cache table. *)

  val with_cache : 'a t -> (Expr.term -> Expr.term -> 'a) ->
    Expr.term -> Expr.term -> 'a
  (** Wraps the given function with the given cache. *)

end

(** {2 Robinson unification} *)

module Robinson : sig

  exception Impossible_ty of Expr.ty * Expr.ty
  exception Impossible_term of Expr.term * Expr.term

  val ty : t -> Expr.ty -> Expr.ty -> t
  val term : t -> Expr.term -> Expr.term -> t
  (** Robinson unification with input substitution. Can be used to extend substitutions.
      Fixpoint computation should be applied to substitutions returned by these functions.
      @raise Impossible_ty _
      @raise Impossible_term _ *)

  val find : section:Section.t -> Expr.term -> Expr.term -> t option
  (** Tries and find a unifier. *)

  val unify_ty : section:Section.t -> (t -> unit) -> Expr.ty -> Expr.ty -> unit
  val unify_term : section:Section.t -> (t -> unit) -> Expr.term -> Expr.term -> unit
  (** Unification on types and terms. Expects a function to deal with
      the substitution if one is found. Currently uses robinson unification. *)

end

