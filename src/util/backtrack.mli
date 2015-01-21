module Stack :
sig
  type t
  type level
  val create : unit -> t
  val dummy_level : level
  val level : t -> level
  val backtrack : t -> level -> unit
  val register_undo : t -> (unit -> unit) -> unit
  val register1 : t -> ('a -> unit) -> 'a -> unit
  val register2 : t -> ('a -> 'b -> unit) -> 'a -> 'b -> unit
  val register3 : t -> ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit
  val register_set : t -> 'a ref -> 'a -> unit
end

module HashtblBack :
  functor (K : Hashtbl.HashedType) ->
  sig
    type key = K.t
    type 'a t
    val create : ?size:int -> Stack.t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val find : 'a t -> key -> 'a
    val remove : 'a t -> key -> unit
    val fold : 'a t -> (key -> 'a -> 'b -> 'b) -> 'b -> 'b
  end
