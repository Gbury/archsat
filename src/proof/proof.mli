
(** Proof utilities

    Provides various utilities for proof output.
*)

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


(** {2 Local Contexts} *)

module Ctx : sig

  type t
  (** The type of a proof context. *)

  type wrapper = (Format.formatter -> unit -> unit) ->
    Format.formatter -> (Expr.formula * Expr.formula) -> unit
  (** A wrapper wraps the function that typically prints the name of the formula,
      so that it can take into account the implicit equivalence relation used.
      The wrapper is given the pair of the current formula whose name is being printed,
      and the formula for which the name was created.
      For instance, it might be used to strategically insert equality symmetry
      whenever necessary). *)

  val mk : ?wrapper:wrapper -> prefix:string -> t
  (** The empty context, takes as argument the prefix to give to the names. *)

  val intro : t -> Format.formatter -> Expr.formula -> unit
  (** Generated a name for the formula, register it, and print it. *)

  val named : t -> Format.formatter -> Expr.formula -> unit
  (** Print the formula's registered name. *)

  (** {5 Advanced functions} *)

  val add : t -> Expr.formula -> unit
  (** Add a formula to the map, a new name is automatically generated for it. *)

  val name : t -> Expr.formula -> string
  (** Find the name associated to a formula in a map (including wrapper). *)

  val find : t -> Expr.formula -> Expr.formula * string
  (** Find the name, and original formula associated to a formula in a map.
      Useful to retrieve data from tags. *)

  val new_name : t -> string
  (** Generate a fresh name, not linked to any particular formula. *)

end

