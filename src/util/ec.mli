
module type Key = sig
    type t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
end

module type S = sig
  type t
  type var

  exception Unsat of var * var * var list

  val create : Backtrack.Stack.t -> t

  val find : t -> var -> var
  val find_tag : t -> var -> var * (var * var) option

  val add_eq : t -> var -> var -> unit
  val add_neq : t -> var -> var -> unit
  val add_tag : t -> var -> var -> unit
end

module Make(T : Key) : S with type var = T.t
