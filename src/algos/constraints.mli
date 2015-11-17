
(** Axiomatic Constraints accumulators *)

type 'a gen = unit -> 'a option
(** A type for generators of elements *)

type 'a fold = 'a gen -> Expr.formula list -> 'a gen
(** Given an enumeration of constraints (of type 'a), and a list of formulas,
    functions of this type should return an enumeration of constraints which rafines
    the given enumeration so that it also contradicts the conjunction of the given formulas *)

(** {2 Axiomatic constraints}
    Taken from a paper from FroCos 2015. TODO: insert correct reference. *)

type t
(** A type for accumulating constraints *)

val make : 'a gen -> 'a fold -> t option
(** Given a generator and a fold function, returns the associated constraint.
    Forces evaluation of the first element of the generator, and returns [None]
    is the given generator is empty. *)

val add_constraint : t -> Expr.formula list -> t option
(** Add a new set of constraints, see the definition of the fold type. This function
    forces the evaluation of the first element of the resulting enumeration of constraints. *)

(** {2 Helpers} *)

val from_merger : (Expr.formula list -> 'a gen) -> ('a * 'a -> 'a gen) -> t
(** [from_merger gen m] returns a fold function, given a function [gen] which generates
    an enumeration of constraints for invalidating a conjunction of formulas, and a function
    [m] which computes the intersection of two constraints. As a special case, [gen] will be
    called on the empty list to generate the 'empty' constraint.
    @raise [Invalid_argument "Constraints.from_merger"] if the generator [gen \[\]] is empty. *)

