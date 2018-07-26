
(** Extension for instanciation *)

(** {2 Proof helpers} *)

type lemma_info = Formula of Expr.formula * Mapping.t * Expr.formula *
                             Expr.ttype Expr.id list * Expr.ty Expr.id list
(** Lemma information for instanciation. Takes a triplet [(f, m, q, tys, ts)], such
    that [q] is the result of instantiating [f] with the bound variables of [m],
    and then quantifying over the variables in [tys] and [ts]. *)


(** {2 Extension helpers} *)

val mark_meta : Expr.formula -> Expr.formula -> unit
(** [make_meta quant f] marks the quantified formula [quant] as having generated
    some metas, resulting in the instanciated [f] formula. This is necessary in
    order to to split mappings in {!partition}. *)

val generalize : Mapping.t -> Mapping.t
(** Introduce virtual meta-variables to replace free variables and meta-variables. *)

val partition : Mapping.t -> Mapping.t list
(** Splits an arbitray unifier into a list. Each unifiers u in the list
    is such that in the set of formulas that generated the metas in u, all formula
    are comparable according to compare_quant.
    Additionally, no formula generating metas from two different unifiers in the list
    are comparable. *)

val add : ?name:string -> ?delay:int -> ?score:int -> Mapping.t -> bool
(** Add a unifier to the list of instanciations to do, possibly giving it a score.
    Unifiers with lower scores are prioritized when pushing instanciations to the solver.
    Returns true if the unifier has been added to the queue of instanciations to do,
    and false otherwise (for instance, if it already belongs to the queue).
    @param mark if true then the formulas will be marked using mark_meta to annotate
            that this is a meta creation. *)

val force : ?name:string -> ?delay:int -> ?score:int -> Expr.formula -> Mapping.t -> bool
(** Specific version of add for the meta extension. *)

val soft_subst :
  name:string -> Expr.formula -> Mapping.t -> Expr.formula list * Dispatcher.lemma
(** [soft_subst f u], returns a clause and lemma suitable for pushing to the solver.
    The clause represents the instanciation of [f] using the mapping [u]. Only the
    top of the formula is instanciated (i.e the first type binder, *and* the first
    term binder, when the mapping contains both type and terms substitutions).
    @param name give a specific name for the proof (used most notably in printing
            proof, such as for the dot output)
    @param mark if true then the formulas will be marked using mark_meta to annotate
            that this is a meta creation. *)

(** {2 Plugin} *)

val register : unit -> unit
(** Register the extension. *)

