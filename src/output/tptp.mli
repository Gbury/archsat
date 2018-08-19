(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** TPTP export

    This module defines helprs for printing tptp problem files.
*)

(** {2 Printing} *)

module Print : sig

  val pos : Pretty.pos Expr.tag
  val name : Pretty.name Expr.tag
  val assoc : Pretty.assoc Expr.tag
  (** Pretty-printing tags. *)

  val var : Format.formatter -> _ Expr.id -> unit
  val cst : Format.formatter -> _ Expr.id -> unit
  (** Print an identifier (using correct escape rules). *)

  val term : Format.formatter -> Term.t -> unit
  (** Print a term in coq syntax. *)

end


(** {2 Printing declarations} *)

val init : Format.formatter -> Options.opts -> unit
(** Print some prefix for the proof (mainly some
    generic info, to make the proof look better). *)

val declare_id :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter ->
  (Dolmen.Id.t * Term.id) -> unit
(** Declare a new identifier, with the correct type. *)

val declare_hyp :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val declare_goal :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> Term.id -> unit
(** Declare a new hypothesis, with the correct type. *)

val declare_solve :
  ?loc:Dolmen.ParseLocation.t -> Format.formatter -> unit -> unit

