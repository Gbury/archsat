(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Formal resolution proofs

    This modules aims at transforming resolution proofs
    coming from mSAT into complete formal proofs.
*)

val compute :
  Options.proof_options -> Proof.sequent -> (Solver.id option * Solver.Proof.proof) -> Proof.proof
(** Compute the formal proof from a starting sequent and a resolution proof. *)

val msat_backend :
  Options.proof_options -> Proof.sequent -> (Solver.id option * Solver.Proof.proof) -> Proof.proof
(** Compute the formal proof from a starting sequent and a resolution proof. *)

