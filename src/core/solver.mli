

module S : sig
    type res =
      | Sat
      | Unsat

    val assume : Expr.formula list list -> unit

    val solve : unit -> res

end
