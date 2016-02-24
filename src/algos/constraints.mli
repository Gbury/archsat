
(** Axiomatic Constraints accumulators *)

type ('a, 'b) refiner = 'b -> 'a -> 'a Gen.t
(** Given a value [t] of type ['b], and a constraint of type ['a],
    functions of this type should return an enumeration of constraints which refines
    the given constraint so that it also contradicts the formulas in [t]. *)

(** {2 Axiomatic constraints}
    Taken from a paper from FroCos 2015. TODO: insert correct reference. *)

type ('a, 'b) t
(** A type for accumulating constraints *)

val make : 'a Gen.t -> ('a, 'b) refiner -> ('a, 'b) t option
(** Given a generator and a fold function, returns the associated constraint.
    Forces evaluation of the first element of the generator, and returns [None]
    is the given generator is empty. *)

val add_constraint : ('a, 'b) t -> 'b -> ('a, 'b) t option
(** Add a new set of constraints, see the definition of the fold type. This function
    forces the evaluation of the first element of the resulting enumeration of constraints. *)

(** {2 Getters} *)

val gen  : ('a, _) t -> 'a Gen.t
(** Returns the generator associated to a constraint *)

(** {2 Helpers} *)

val from_merger : ('b -> 'a Gen.t) -> ('a -> 'a -> 'a Gen.t) -> 'a Gen.t -> ('a, 'b) t
(** [from_merger gen m start] returns a fold function, given a function [gen] which generates
    an enumeration of constraints for invalidating a conjunction of formulas, and a function
    [m] which computes the intersection of two constraints. *)

val dumps :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> ('a, 'b) t list -> unit
(** Return a dot graph of the succesive accumulators. *)

