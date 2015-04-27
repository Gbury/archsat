
type t

val empty : (Unif.t list -> unit) -> t

val add_neq : t -> Expr.term -> Expr.term -> t

val add_eqs : t -> (Expr.term * Expr.term) list -> t

val mk_unifier : (Expr.term * Expr.term) list -> (Unif.t list -> unit) ->
  Expr.term -> Expr.term -> unit

