
(* Unsat core for proofs

   This modules defines helpers for printing unsat cores from a
   mSAT proof.
*)

(** {2 Main} *)

val print : Format.formatter -> Solver.proof -> unit
(** Prints the unsat core of a proof on the given formatter. *)

