
(** Equality closure using an union-find structure.
    This module implements a equality closure algorithm using an union-find structure.
    It supports adding of equality as well as inequalities, and raises exceptions
    when trying to build an incoherent closure.
    Please note that this does not implement congruence closure, as we do not
    look inside the terms we are given. *)

module type Key = sig
    (** The type of keys used by the equality closure algorithm *)

    type t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val debug : Buffer.t -> t -> unit
end

module type S = sig
  (** Type signature for the equality closure algorithm *)

  (** {3 Type definitions} *)

  type var
  (** The type of expressions on which equality closure is built *)

  type 'a t
  (** Mutable state of the equality closure algorithm.
      The type parameter ['a] is the type of payloads attached to
      equivalence classes. *)

  type 'a repr
  (** The type of equivalence classes. Parametrised
      by the type of payloads attached to it. *)

  exception Unsat of var * var * var list
  (** Raise when trying to build an incoherent equality closure, with an explanation
      of the incoherence.
      [Unsat (a, b, l)] is such that:
      - [a <> b] has been previously added to the closure.
      - [l] start with [a] and ends with [b]
      - for each consecutive terms [p] and [q] in [l],
        an equality [p = q] has been added to the closure.
  *)

  (** {3 Accessors} *)

  val repr : 'a repr -> var
  (** Return the representant of an equivalence class. *)

  val load : 'a repr -> 'a
  (** Return the payload of an equivalence class. *)

  (** {3 Union-find structure} *)

  val create :
    gen:(var -> 'a) -> merge:('a -> 'a -> 'a) ->
    section:Util.Section.t -> Backtrack.Stack.t -> 'a t
  (** Creates an empty state which uses the given backtrack stack *)

  val get_repr : 'a t -> var -> 'a repr
  (** Get the representant of the equivalence class of a variable. *)

  val find : 'a t -> var -> var
  (** Returns the representative of the given expression in the current closure state *)

  val add_eq : 'a t -> var -> var -> unit
  val add_neq : 'a t -> var -> var -> unit
  (** Add an equality of inequality to the closure. *)

  val add_tag : 'a t -> var -> var -> unit
  (** Add a tag to an expression. The algorithm ensures that each equality class
      only has one tag. If incoherent tags are added, an exception is raised. *)

  val find_tag : 'a t -> var -> var * (var * var) option
  (** Returns the tag associated with the equality class of the given term, if any.
      More specifically, [find_tag e] returns a pair [(repr, o)] where [repr] is the representant of the equality
      class of [e]. If the class has a tag, then [o = Some (e', t)] such that [e'] has been tagged with [t] previously. *)

end

module Eq(T : Key) : S with type var = T.t

