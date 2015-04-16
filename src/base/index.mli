
type t

val empty : t

val add : Expr.term -> t -> t

val find : Expr.term -> t -> Expr.term list


