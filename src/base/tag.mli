
(** Tags *)

(** {2 Type definitions} *)

type map
(** The type of immutable maps from tags to values. *)

type 'a t
(** A tag containing values of type ['a]. *)

(** {2 Creating and accessing tags} *)

val empty : map
(** The empty map. *)

val create : unit -> 'a t
(** Create a new tag. *)

val get : map -> 'a t -> 'a option
(** Get the value of a tag (if it exists). *)

val add : map -> 'a t -> 'a -> map
(** Add a value to a tag in a map. *)

