
(** Backtrack state wth stack *)

type 'a t
(** A stack of states of type 'a *)

type level = private int
(** The type of level for backtrack functions *)

val base : 'a -> 'a t
(** Returns the stack containing a single state *)

val top : 'a t -> 'a
(** Returns the current state, i.e the top of the stack *)

val update : 'a t -> ('a -> 'a) -> unit
(** Updates the state at the top of the stack with the given function *)

val current_level : 'a t -> level
(** Increase the size of the stack by 1, returning the current size of the stack *)

val backtrack : 'a t -> level -> unit
(** Backtracks (in place) to the given level *)
