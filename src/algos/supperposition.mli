
type t

val empty : (Unif.t list -> unit) -> t

val add_eq : t -> Expr.term -> Expr.term -> t

val add_neq : t -> Expr.term -> Expr.term -> t

val solve : t -> t

