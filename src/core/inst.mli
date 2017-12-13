
(** Extension for instanciation *)

(** {2 Proof helpers} *)

type lemma_info = Formula of Expr.formula * Mapping.t * Expr.formula
(** Lemma information for instanciation. Takes a triplet [(f, m, q)], such
    that [q] is the result of instantiating [f] with the bound variables of [m]. *)

(*
val coq_proof : lemma_info -> Coq.tactic
(** Return a coq proof from a lemma. *)
*)


(** {2 Extension helpers} *)

val partition : Mapping.t -> Mapping.t list
(** Splits an arbitray unifier into a list. Each unifiers u in the list
    is such that in the set of formulas that generated the metas in u, all formula
    are comparable according to compare_quant.
    Additionally, no formula generating metas from two different unifiers in the list
    are comparable. *)

val add : ?delay:int -> ?score:int -> Mapping.t -> bool
(** Add a unifier to the list of instanciations to do, possibly giving it a score.
    Unifiers with lower scores are prioritized when pushing instanciations to the solver.
    Returns true if the unifier has been added to the queue of instanciations to do,
    and false otherwise (for instance, if it already belongs to the queue). *)

val soft_subst : Expr.formula -> Mapping.t -> Expr.formula list * Dispatcher.lemma
(** [soft_subst f u], returns a clause and lemma suitable for pushing to the solver.
    The clause represents the instanciation of [f] using the mapping [u]. Only the
    top of the formula is instanciated (i.e the first type binder, *and* the first
    term binder, when the mapping contains both type and terms substitutions). *)

(** {2 Plugin} *)

val register : unit -> unit
(** Register the extension. *)

