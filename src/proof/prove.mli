
(** Proving utilities

    Wrappers for proof type-defs, definitions, axioms,
    and general global state. *)


(** {2 Global Proof contexts} *)

val add_hyp : Dolmen.Id.t -> Expr.formula list -> unit
(** Record the given named hypothesis to the global context. *)

val find_hyp : Dolmen.Id.t -> Expr.formula list
(** Find an hypothesis in the global context. *)

val add_goal : Dolmen.Id.t -> Expr.formula -> unit
(** Add a goal to the context *)

val clear_goals : unit -> unit
(** Clear the current list of goals. *)

val get_goals : unit -> (Dolmen.Id.t * Expr.formula) list
(** Get all current goals from the context, together with
    current context. *)

