

val instanciation : Dispatcher.id -> Unif.t ->
    ((Expr.formula list) * Dispatcher.proof) list
(** Takes an id and a unifier, and returns a list of clauses ready to be pushed,
    along with their proof indications. The unifier argument should have
    been split and completed according to the corresponding Unif fonctions. *)

