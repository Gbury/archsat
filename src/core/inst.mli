

val instanciation : Dispatcher.id ->
    (Expr.ty Expr.meta * Expr.term) list ->
    ((Expr.formula list) * Dispatcher.proof)
(** Takes an id and a (partial) list of instanciations,
    and returns a clause ready to be pushed,
    along with its proof indication *)

