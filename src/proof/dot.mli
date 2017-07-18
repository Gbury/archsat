
(* Proofs in the DOT format

   This modules defines helpers for printing dot graphs represneting
   unsat proofs.
*)

(** {2 Main} *)

val print : Format.formatter -> Solver.proof -> unit
(** Prints the unsat core of a proof on the given formatter. *)

