
(**
   mSAT solver instanciated with Dispatcher Plugin.
   See {{: https://github.com/Gbury/mSAT} mSAT}
   for more information on mSAT.
*)

(** {2 Core solver} *)

type level

type proof
(** The abstract type of proofs given by the solver. *)

type res =
  | Sat
  | Unsat
  | Unknown
  (** Type of results returned by the solver *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)

val assume : Expr.formula list list -> unit
(** Add a list of assumptions as cnf formulas. *)

val push : unit -> level
(** Stores the current set of assumptions and returns the associated level *)

val pop : level -> unit
(** Restore the solver to a stat equivalent to the one it was at the moment
    [push] returned the level. *)

val model : unit -> (Expr.term * Expr.term) list
(** Returns the current model of the sat solver.
    Contains only the variables and applications of uninterpreted functions. *)

val full_model : unit -> (Expr.term * Expr.term) list
(** Returns the current full model of the sat solver. *)

val get_proof : unit -> proof
(** Returns a proof of unsatisfiability of the current assumptions. *)

val print_dot_proof : Format.formatter -> proof -> unit
(** Prints the proof on the given formatter. *)

(** {2 Restart & Replay} *)

exception Restart

type ret =
  | Ok
  | Toggle of string

type _ Dispatcher.msg += Found : res -> ret Dispatcher.msg
(** Once an Unsat result has been found, this message is sent to all
    extensions. If an extension answers something different than [None],
    then the sat solver is rolled back, and the solving restarts.
    The goal of this message is for isntance, to allow extensions to do some smart
    on the first try, and then replay the solving so that a correct proof might
    be output. *)


