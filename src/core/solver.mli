
(** mSAT solver instanciated with Dispatcher Plugin *)

type res =
  | Sat
  | Unsat
  (** Type of results returned by the solver *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)

val assume : Expr.formula list list -> unit
(** Add a list of assumptions as cnf formulas. *)

val model : unit -> (Expr.term * Expr.term) list
(** Returns the current model of the sat solver.
    Contains only the variables and applications of uninterpreted functions. *)

val full_model : unit -> (Expr.term * Expr.term) list
(** Returns the current full model of the sat solver. *)


