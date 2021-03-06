(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    and terms corresponding to unsatisfiability proofs.
*)

(** {2 Printing} *)

module Print : sig

  val pos : Pretty.pos Expr.tag
  val name : Pretty.name Expr.tag
  val assoc : Pretty.assoc Expr.tag
  (** Pretty-printing tags. *)

  val id : Format.formatter -> _ Expr.id -> unit
  (** Print an identifier (using correct escape rules). *)

  val term : Format.formatter -> Term.t -> unit
  (** Print a term in coq syntax. *)

  val fragile : Format.formatter -> Term.t -> unit
  (** Print a fragile term *)

  val bigterm : Format.formatter -> Term.t -> unit
  (** Print a big term (i.e, with less indentation and boxes).
      This should help formatting of big terms where indentation box
      have a tendency to push everything to the right, and also
      help performances since there are less boxes open at the same time. *)

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

val declare_goal :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val declare_goal_term :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val proof_context :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a -> unit
(** Wraps a printer to make it print inside a proof context. *)

val proof_term_context :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a -> unit
(** Wraps a printer to make it print inside a proof context. *)

