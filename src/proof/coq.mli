
(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    corresponding to unsatisfiability proofs.
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

end


(** {2 Printing proofs} *)

val declare_id : Format.formatter -> Term.id -> unit
(** Declare a new identifier, with th corrct type. *)


