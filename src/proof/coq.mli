
(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    corresponding to unsatisfiability proofs.
*)

(** {2 Printing} *)

module Print : sig

  val pos : Pretty.pos Expr.tag
  val name : Pretty.name Expr.tag
  val assoc : Pretty.assoc Expr.tag

  val dolmen : Format.formatter -> Dolmen.Id.t -> unit

  val id : Format.formatter -> _ Expr.id -> unit

  val term : Format.formatter -> Term.t -> unit

end

