
module type S = sig

    type key
    type 'a t
    type level

    val create : int -> 'a t

    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a

    val fold : 'a t -> (key -> 'a -> 'b -> 'b) -> 'b -> 'b

    val dummy_level : level
    val current_level : 'a t -> level
    val backtrack : 'a t -> level -> unit
end

module Make(T : Hashtbl.HashedType) : S with type key = T.t and type level = int
