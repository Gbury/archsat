
(* Proofs in the DOT format

   This modules defines helpers for printing dot graphs represneting
   unsat proofs.
*)

(** {2 Dispatcher messages} *)

type _ Dispatcher.msg +=
  | Info : Dispatcher.lemma_info ->
    (string option * ((Format.formatter -> unit -> unit) list)) Dispatcher.msg (**)
(** Sent to the extension that produced a proof, asks for an optional color,
    and a list of custom formatters to print additional information about the lemma. *)

(** {2 Printing expressions} *)

module Print : sig
  val id : Format.formatter -> _ Expr.id -> unit
  val meta : Format.formatter -> _ Expr.meta -> unit

  val ty : Format.formatter -> Expr.ty -> unit
  val term : Format.formatter -> Expr.term -> unit
  val formula : Format.formatter -> Expr.formula -> unit

  val mapping : Format.formatter -> Mapping.t -> unit
end

(** {2 Main} *)

val print : Format.formatter -> Solver.proof -> unit
(** Prints the unsat core of a proof on the given formatter. *)

