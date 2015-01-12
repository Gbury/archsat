
module type S = sig
  type t
  type var

  exception Unsat of var * var * var list

  val empty : t
  val find : t -> var -> var
  val add_eq : t -> var -> var -> t
  val add_neq : t -> var -> var -> t
end

module Make(T : Map.OrderedType) : S with type var = T.t
