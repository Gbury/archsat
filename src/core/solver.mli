
module S : sig

  type res =
    | Sat
    | Unsat

  val solve : unit -> res
  val assume : Expr.formula list list -> unit

end
