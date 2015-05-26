
(** Provide instantiation helpers. *)

val split : Unif.t -> Unif.t list
(** Splits an arbitray unifier into a list. Each unifiers u in the list
    is such that in the set of formulas that generated the metas in u, all formula
    are comparable according to compare_quant.
    Additionally, no formula generating metas from two different unifiers in the list
    are comparable. *)

val simplify : Unif.t -> Unif.t
(** Simplifies the given unifier to eliminate metas that can not be instanciated directly. *)

val add : ?delay:int -> ?score:int -> Unif.t -> bool
(** Add a unifier to the list of instanciations to do, possibly giving it a score.
    Unifiers with lower scores are prioritized when pushing instanciations to the solver.
    Returns true if the unifier has been added to the queue of instanciations to do,
    and false otherwise (forinstance, if it already belongs to the queue). *)

