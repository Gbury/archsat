
(** Proving utilities

    Wrappers for proof type-defs, definitions, axioms,
    and general global state. *)

val declare_ty : Options.proof_options -> Expr.Id.TyCstr.t -> unit
(** Declare a type constructor. *)

val declare_term : Options.proof_options -> Expr.Id.Const.t -> unit
(** Declare a new constant symbol. *)

val declare_hyp : Options.proof_options -> Term.id -> unit
(** Declare a new hyp. *)

val declare_goal : Options.proof_options -> Term.id -> Expr.formula -> unit
(** Declare a goal. *)

val output_proof : Options.proof_options -> Solver.proof -> unit
(** Output the proof on all relevant files according to options. *)


