
(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    corresponding to unsatisfiability proofs.
*)

(** {2 Dispatcher messages} *)

type _ Dispatcher.msg +=
  | Prove : Format.formatter * string * Dispatcher.lemma_info -> unit Dispatcher.msg (**)
(** Sent to the extension that produced a proof; asks for it to prove the
    clause/lemma it produced, using a coq script which should introduce
    the clause as an hypothesis with the given name. *)

(** {2 Printing expressions} *)

module Print : sig

  val id : Format.formatter -> _ Expr.id -> unit
  val meta : Format.formatter -> _ Expr.meta -> unit
  val dolmen : Format.formatter -> Dolmen.Id.t -> unit

  val ty : Format.formatter -> Expr.ty -> unit
  val term : Format.formatter -> Expr.term -> unit
  val formula : Format.formatter -> Expr.formula -> unit

end

(** {2 Main} *)

val declare_ty : Format.formatter -> Expr.ttype Expr.function_descr Expr.id -> unit
val declare_term : Format.formatter -> Expr.ty Expr.function_descr Expr.id -> unit
(** Print the type declarations for constant symbols *)

val add_hyp : Format.formatter -> (Dolmen.Id.t * Expr.formula) -> unit
(** Print an hypothesis/axiom *)

val add_goal : Format.formatter -> (Dolmen.Id.t * Expr.formula) -> unit
(** Add the goal to the list of goals the next proof will prove. *)

val print_proof : context:bool -> Format.formatter -> Solver.proof -> unit
(** Print a theorem, proving the named goals previously added using the given proof. *)


