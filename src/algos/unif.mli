(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Unification for expressions *)

(** {2 Unification helpers} *)

val to_formula : Mapping.t -> Expr.formula
(** Generate a conjunction of all bindings of the substitution as equalities *)

val occurs_check : Mapping.t -> bool
(** Occur check on mappings. *)

val occurs_ty :
  Mapping.t ->
  Expr.Id.Ttype.t list ->
  Expr.Meta.Ttype.t list -> Expr.ty -> bool
val occurs_term :
  Mapping.t ->
  Expr.Id.Ty.t list ->
  Expr.Meta.Ty.t list -> Expr.term -> bool
(** Specialized variant of occurs_check *)

val follow_ty : Mapping.t -> Expr.ty -> Expr.ty
val follow_term : Mapping.t -> Expr.term -> Expr.term
(** Follow the mapping as long as the head symbol of the given type/term
    is a meta with a binding in the mapping. *)


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
  exception Impossible_atomic of Expr.formula * Expr.formula

  val ty : Mapping.t -> Expr.ty -> Expr.ty -> Mapping.t
  val term : Mapping.t -> Expr.term -> Expr.term -> Mapping.t
  val atomic : Mapping.t -> Expr.formula -> Expr.formula -> Mapping.t list
  (** Robinson unification with input substitution. Can be used to extend substitutions.
      Fixpoint computation should be applied to substitutions returned by these functions.
      @raise Impossible_ty _
      @raise Impossible_term _
      @raise Impossible_atomic _ *)

  val find : section:Section.t -> Expr.term -> Expr.term -> Mapping.t option
  (** Tries and find a unifier. *)

  val unify_ty : section:Section.t -> (Mapping.t -> unit) -> Expr.ty -> Expr.ty -> unit
  val unify_term : section:Section.t -> (Mapping.t -> unit) -> Expr.term -> Expr.term -> unit
  (** Unification on types and terms. Expects a function to deal with
      the substitution if one is found. Currently uses robinson unification. *)

end

