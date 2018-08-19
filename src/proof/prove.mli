(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Proving utilities

    Wrappers for proof type-defs, definitions, axioms,
    and general global state. *)

exception Hypothesis_name_conflict of
    (Term.id * Dolmen.ParseLocation.t option) *
    (Term.id * Dolmen.ParseLocation.t option)
(** Exception raised when two hypothesis have the same name. *)

(** {2 Managings proof state} *)

val init : Options.opts -> unit -> unit
(** Initialize the formatters for proof output. *)

val add_implicit : Term.id -> unit
(** Add a new implicit symbol. *)

val declare_id :
  ?loc:Dolmen.ParseLocation.t -> Options.proof_options ->
  Term.id list -> Term.id -> unit
(** Declare a type constructor. *)

val declare_hyp :
  ?loc:Dolmen.ParseLocation.t -> Options.proof_options ->
  Dolmen.Id.t -> Term.id list -> Term.id -> unit
(** Declare a new hyp. *)

val declare_goal :
  ?loc:Dolmen.ParseLocation.t -> Options.proof_options ->
  Dolmen.Id.t -> Term.id list -> (Solver.id * Term.id) -> unit
(** Declare a goal. *)

val output_proof : Options.proof_options -> Solver.proof -> unit
(** Output the proof on all relevant files according to options. *)


