
type map
type 'a t

val new_tag : unit -> 'a t

val empty : map
val get : map -> 'a t -> 'a option
val add : map -> 'a t -> 'a -> map

