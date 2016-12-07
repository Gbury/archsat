
(**
   mSAT solver instanciated with Dispatcher Plugin.
   See {{: https://github.com/Gbury/mSAT} mSAT}
   for more information on mSAT.
*)

(** {2 Type defs} *)

type proof
(** The type of proofs. *)

type model
(** The type of models. *)

type view = (Expr.formula -> unit) -> unit
(** A view of the trail when the solver has reached SAT *)

type res =
  | Sat of model
  | Unsat of proof
  | Unknown
(** Type of results returned by the solver *)


(** {2 Core solver} *)

val assume : Expr.formula list list -> unit
(** Add some clauses to the current problem. *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)


(** {2 Dispatcher messages} *)

type unsat_ret =
  | Unsat_ok

type sat_ret =
  | Sat_ok
  | Restart
  | Assume of Expr.formula list

type _ Dispatcher.msg +=
  | Found_sat : view -> sat_ret Dispatcher.msg
  | Found_unsat : proof -> unsat_ret Dispatcher.msg
  | Found_unknown : unit -> unit Dispatcher.msg
(** Dispatcher messages. *)

