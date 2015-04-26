
type t
(*
type res =
  | Model of t
  | Found of Unif.t list

val add_neq : t -> Expr.term -> Expr.term -> res

val add_eqs : t -> (Expr.term * Expr.term) list -> res

   *)
val mk_unifier : (Expr.term * Expr.term) list -> (Unif.t -> unit) ->
  (Expr.term -> Expr.term -> unit)
