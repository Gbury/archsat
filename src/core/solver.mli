
(** mSAT solver instanciated with Dispatcher Plugin *)

type res =
  | Sat
  | Unsat
  (** Type of results returned by the solver *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)

val assume : Expr.formula list list -> unit
(** Add a list of assumptions as cnf formulas. *)

