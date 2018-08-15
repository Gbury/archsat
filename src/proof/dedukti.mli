
(** Proof in the Dedukti format

    This module defines helprs for printing dedukti proof terms
    corresponding to unsatisfiability proofs.
*)

(** {2 Printing} *)

module Print : sig

  val pos : Pretty.pos Expr.tag
  val name : Pretty.name Expr.tag
  val assoc : Pretty.assoc Expr.tag
  (** Pretty-printing tags. *)

  val variant : (Term.t list -> Term.t * Term.t list) Expr.tag
  (** Provide opportunity to have variants of a given function symbol. *)

  val id : Format.formatter -> _ Expr.id -> unit
  (** Print an identifier (using correct escape rules). *)

  val term : Format.formatter -> Term.t -> unit
  (** Print a term in coq syntax. *)

  val fragile : Format.formatter -> Term.t -> unit
  (** Print a fragile term *)

end


(** {2 Printing proofs} *)

val init : Format.formatter -> Options.opts -> unit
(** Print some prefix for the proof (mainly some
    generic info, to make the proof look better). *)

val declare_id :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new identifier, with the correct type. *)

val declare_hyp :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val declare_goal_term :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val proof_term_context :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a -> unit
(** Wraps a printer to make it print inside a proof context. *)

