
(** mSAT solver instanciated with Dispatcher Plugin *)

type proof
(** The abstract type of proofs given by the solver. *)

type res =
  | Sat
  | Unsat
  (** Type of results returned by the solver *)

val get_options : unit -> (Arg.key * Arg.spec * Arg.doc) list
(** Returns a list of command-line options to be added. *)

val preprocess : Expr.formula -> unit
(** Preprocess the given formula. All formulas should be preprocessed
    before being assumed. *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)

val assume : Expr.formula list list -> unit
(** Add a list of assumptions as cnf formulas. *)

val model : unit -> (Expr.term * Expr.term) list
(** Returns the current model of the sat solver.
    Contains only the variables and applications of uninterpreted functions. *)

val full_model : unit -> (Expr.term * Expr.term) list
(** Returns the current full model of the sat solver. *)

val get_proof : unit -> proof
(** Returns a proof of unsatisfiability of the current assumptions. *)

val print_proof_dot : Format.formatter -> proof -> unit
(** Prints the proof on the given formatter. *)
