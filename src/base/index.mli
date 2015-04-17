
type t

val empty : t

val add : Expr.term -> t -> t

val remove : Expr.term -> t -> t

val get : Expr.term -> t -> Expr.term list

