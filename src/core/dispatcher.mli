
(** Plugin Manager *)

type lemma = private {
  plugin_name : string;
  proof_name : string;
  proof_ty_args : Expr.ty list;
  proof_term_args : Expr.term list;
  proof_formula_args : Expr.formula list;
}

include Msat.Plugin_intf.S with
  type term = Expr.term and
  type formula = Expr.formula and
  type proof = lemma
(** This module is a valid Plugin for Mcsat *)

(** {2 Exceptions} *)

exception Not_assigned of term
(** The given term does not have a current assignment *)

exception Bad_assertion of string
(** Expected some invariant but didn't get it. Raised in place of
    'assert false'. *)

exception Absurd of formula list * proof
(** To be used by extensions in their 'assume' function *)

(** {2 Proof management} *)

val mk_proof : string ->
  ?ty_args : Expr.ty list ->
  ?term_args : Expr.term list ->
  ?formula_args : Expr.formula list ->
  string -> proof
(** Returns the associated proof. Optional arguments not specified are assumed ot be empty lists. *)

(** {2 Extension Registering} *)

type ext
(** Type of plugins/extensions *)

val mk_ext :
  section:Util.Section.t ->
  ?peek:(formula -> unit) ->
  ?if_sat:(((formula -> unit) -> unit) -> unit) ->
  ?assume:(formula * int -> unit) ->
  ?eval_pred:(formula -> (bool * int) option) ->
  ?preprocess:(formula -> (formula * proof) option) -> unit -> ext
(** Generate a new extension with defaults values. *)

module Plugin : Extension.S with type ext = ext

(** {2 Solver functions} *)

val pre_process : formula -> formula
(** Give the formula to extensions for pre-processing. *)

(** {2 Extension-side helpers} *)

val section : Util.Section.t
(** Debug Section for the dispatcher *)

val stack : Backtrack.Stack.t
(** The global undo stack. All extensions should either use datatypes
    compatible with it (like Backtrack.HashtblBack), or register
    undo actions with it. *)

val push : formula list -> proof -> unit
(** Push the given clause to the sat solver. *)

val propagate : formula -> int -> unit
(** Propagate the given formula at the given evaluation level. *)

(** {2 Assignment functions} *)

val get_assign : term -> term * int
(** [get_assign t] Returns the current assignment of [t] and its level, if it exists.
    @raise Not_assigned if the term isn't assigned *)

val set_assign : term -> term -> int -> unit
(** [set_assign t v lvl] sets the assignment of [t] to [v], with level [lvl].
    May erase previous assignment of [t]. *)

val watch : ?formula:formula -> string -> int -> term list -> (unit -> unit) -> unit
(** [watch tag k l f] sets up a k-watching among the terms in l, calling f once there is fewer
    than k terms not assigned in l. The pair [(l, tag)] is used as a key to eliminate duplicates.
    @param formula attach the watcher to a formula, so that the callback will onlybe called
      if the given formula is among the current assumption when the watcher triggers. *)

val model : unit -> (term * term) list
(** Returns the full assignment in the current model. *)

