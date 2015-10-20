
(** Axiomatic Constraints accumulators *)

type 'a gen = unit -> 'a option

(** {2 Streams (for lack of a better name)} *)

type 'a stream
(** A type for non-empty generators. Stores the first element of a generator. *)

val stream_of_gen : 'a gen -> 'a stream option
(** Takes a generator and try and convert it to a stream. Returns [None] if the generator is empty.
    Forces the evaluation of the first element of the generator. *)

val gen_of_stream : 'a stream -> 'a gen
(** Returns the generator associated to a stream. *)


(** {2 Axiomatic constraints}
    Taken from a paper from FroCos 2015. TODO: insert correct reference. *)

type t
(** A type for accumulating constraints *)

type 'a fold = 'a gen -> Expr.formula list -> 'a gen
(** Given an enumeration of constraints (of type 'a), and a list of formulas,
    functions of this type should return an enumeration of constraints which rafines
    the given enumeration so that it also contradicts the conjunction of the given formulas *)

val from_merger : (Expr.formula list -> 'a gen) -> ('a * 'a -> 'a option) -> 'a fold
(** [from_merger gen m] returns a fold function, given a function [gen] which generates
    an enumeration of constraints for invalidating a conjunction of formulas, and a function
    [m] which computes the intersection of two constraints. *)

val make : 'a stream -> 'a fold -> t
(** Given a stream and a fold function, returns the associated constraint. *)

val add_constraint : t -> Expr.formula list -> t option
(** Add a new set of constraints, see the definition of the fold type. This function
    forces the evaluation of the first element of the resulting enumeration of constraints. *)
