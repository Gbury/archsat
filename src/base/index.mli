
module Make(T: Set.OrderedType) : sig

  type t

  val empty : t

  val add : Expr.term -> T.t -> t -> t

  val remove : Expr.term -> T.t -> t -> t

  val unify : Expr.term -> t -> (Expr.term * Unif.t * T.t list) list

end
