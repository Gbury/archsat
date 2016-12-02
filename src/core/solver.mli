
(**
   mSAT solver instanciated with Dispatcher Plugin.
   See {{: https://github.com/Gbury/mSAT} mSAT}
   for more information on mSAT.
*)

(** {2 Core solver} *)

type proof
(** The type of proofs. *)

type model
(** The type of models. *)

type res =
  | Sat of model
  | Unsat of proof
  | Unknown
(** Type of results returned by the solver *)

val solve : unit -> res
(** Try and solve the current set of assumptions *)

(** {2 Dispatcher messages} *)

type unsat_ret =
  | Unsat_ok

type sat_ret =
  | Sat_ok
  | Assume of Expr.formula list

type _ Dispatcher.msg +=
  | Found_sat : model -> sat_ret Dispatcher.msg
  | Found_unsat : proof -> unsat_ret Dispatcher.msg
  | Found_unknown : unit -> unit Dispatcher.msg
(** Dispatcher messages. *)

