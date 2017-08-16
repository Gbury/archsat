
(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    corresponding to unsatisfiability proofs.
*)

(** {2 Dispatcher messages} *)

module M : Map.S with type key = Expr.formula

type raw_proof = Format.formatter -> unit -> unit

type ordered_proof = {
  order : Expr.formula list;
  proof : raw_proof;
}

type impl_proof = {
  prefix  : string;
  left    : Expr.formula list;
  right   : Expr.formula list;
  proof   : Format.formatter -> string M.t -> unit;
}

type proof_style =
  | Raw of raw_proof
  | Ordered of ordered_proof
  | Implication of impl_proof

type _ Dispatcher.msg +=
  | Prove : Dispatcher.lemma_info -> proof_style Dispatcher.msg (**)
(** Sent to the extension that produced a proof; asks for it to prove the
    clause/lemma it produced, using a coq script.  *)

(** {2 Printing expressions} *)

module Print : sig

  val id : Format.formatter -> _ Expr.id -> unit
  val meta : Format.formatter -> _ Expr.meta -> unit
  val dolmen : Format.formatter -> Dolmen.Id.t -> unit

  val ty : Format.formatter -> Expr.ty -> unit
  val term : Format.formatter -> Expr.term -> unit
  val formula : Format.formatter -> Expr.formula -> unit

  val path : Format.formatter -> int * int -> unit
  val path_to : Format.formatter -> Expr.formula * Expr.f_order -> unit

  val pattern :
    start:(Format.formatter -> unit -> unit) ->
    stop:(Format.formatter -> unit -> unit) ->
    sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> Expr.formula -> unit) ->
    Format.formatter -> Expr.f_order -> unit

  val pattern_or :
    (Format.formatter -> Expr.formula -> unit) ->
    Format.formatter -> Expr.f_order -> unit
  val pattern_and :
    (Format.formatter -> Expr.formula -> unit) ->
    Format.formatter -> Expr.f_order -> unit
  val pattern_intro_and :
    (Format.formatter -> Expr.formula -> unit) ->
    Format.formatter -> Expr.f_order -> unit

end

(** {2 Main} *)

val declare_ty : Format.formatter -> Expr.ttype Expr.function_descr Expr.id -> unit
val declare_term : Format.formatter -> Expr.ty Expr.function_descr Expr.id -> unit
(** Print the type declarations for constant symbols *)

val add_hyp : Format.formatter -> (Dolmen.Id.t * Expr.formula list) -> unit
(** Print an hypothesis/axiom *)

val add_goal : Format.formatter -> (Dolmen.Id.t * Expr.formula) -> unit
(** Add the goal to the list of goals the next proof will prove. *)

val print_proof : Format.formatter -> Solver.proof -> unit
(** Print a theorem, proving the named goals previously added using the given proof. *)


