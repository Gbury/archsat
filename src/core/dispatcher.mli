
(** Plugin Manager *)

(** {2 Types for message} *)

type 'ret msg = ..
(** Messages are arbitrary data that can be sent to extensions, and expect
    an answer of type ['ret option].
    Note that since it is an extensible type, extensions will most likely
    ignore most messages *)

type _ msg += If_sat : ((Expr.formula -> unit) -> unit) -> unit msg
(** This message contains a function to iter over current assumptions.
    It is sent at the end of each round of solving, i.e whenever the sat solver
    returns a model. *)

(** {2 Type for lemmas} *)

type lemma = private {
  plugin_name : string;
  proof_name : string;
  proof_ty_args : Expr.ty list;
  proof_term_args : Expr.term list;
  proof_formula_args : Expr.formula list;
}

(** {2 Solver modules} *)

module SolverExpr : Msat.Expr_intf.S
  with type Term.t = Expr.term
   and type Formula.t = Expr.formula
   and type proof = lemma

module SolverTypes : Msat.Solver_types.S
  with type term = Expr.term
   and type formula = Expr.formula
   and type proof = lemma

module SolverTheory : Msat.Plugin_intf.S
  with type term = Expr.term
   and type formula = Expr.formula
   and type proof = lemma
(** This module is a valid theory for Mcsat *)

(** {2 Exceptions} *)

exception Not_assigned of Expr.term
(** The given term does not have a current assignment *)

exception Bad_assertion of string
(** Expected some invariant but didn't get it. Raised in place of
    'assert false'. *)

exception Absurd of Expr.formula list * lemma
(** To be raised by extensions in their 'assume' function
    when an unsatisfiable set of formulas as been assumed. *)

(** {2 Proof management} *)

val mk_proof : string ->
  ?ty_args : Expr.ty list ->
  ?term_args : Expr.term list ->
  ?formula_args : Expr.formula list ->
  string -> lemma
(** Returns the associated proof. Optional arguments not specified are assumed ot be empty lists.
    First argument is plugin name, last is proof name *)

val proof_debug : lemma -> string * string option * Expr.term list * Expr.formula list
(** Some debug output for lemmas (used for dot output). *)

(** {2 Extension Registering} *)

type ext
(** Type of plugins/extensions *)

type handle = { handle : 'ret. 'ret msg -> 'ret option; }
(** Type for message handlers. Enclosed in a record to ensure full polymorphism *)

val mk_ext :
  section:Util.Section.t ->
  ?handle:handle ->
  ?peek:(Expr.formula -> unit) ->
  ?assume:(Expr.formula -> unit) ->
  ?eval_pred:(Expr.formula -> (bool * Expr.term list) option) ->
  ?preprocess:(Expr.formula -> (Expr.formula * lemma) option) ->
  unit -> ext
(** Generate a new extension with defaults values. *)

module Plugin : Extension.S with type ext = ext

(** {2 Solver functions} *)

val send : unit msg -> unit
(** Send the given message to all extensions, ignoring any exception raised
    during the handling of the message. *)

val handle : ('acc -> 'ret option -> 'acc) -> 'acc -> 'ret msg -> 'acc
(** Fold over the results of handlers for a given message *)

val pre_process : Expr.formula -> Expr.formula
(** Give the formula to extensions for pre-processing. *)

(** {2 Extension-side helpers} *)

val section : Util.Section.t
(** Debug Section for the dispatcher *)

val solver_section : Util.Section.t
(** Debug Section for the Solver *)

val stack : Backtrack.Stack.t
(** The global undo stack. All extensions should either use datatypes
    compatible with it (like Backtrack.HashtblBack), or register
    undo actions with it. *)

val push : Expr.formula list -> lemma -> unit
(** Push the given clause to the sat solver. *)

val propagate : Expr.formula -> Expr.term list -> unit
(** Propagate the given formula at the given evaluation level. *)

val consequence : Expr.formula -> Expr.formula list -> lemma -> unit
(** Propagate the given formula. [consequence f l proof] propagates [f]
    as a consequence of the formulas in [l]. [proof] should be a proof
    of the clause "[l] implies [f]". *)

(** {2 Model operations} *)

val get_truth : Expr.formula -> bool option
(** Returns the current truth value of a given formula, if it is decided. *)

val get_assign : Expr.term -> Expr.term
(** [get_assign t] Returns the current assignment of [t], if it exists.
    @raise Not_assigned if the term isn't assigned *)

val set_assign : Expr.term -> Expr.term -> unit
(** [set_assign t v lvl] sets the assignment of [t] to [v], with level [lvl].
    May erase previous assignment of [t]. *)

val watch : ?formula:Expr.formula -> string -> int -> Expr.term list -> (unit -> unit) -> unit
(** [watch name k l f] sets up a k-watching among the terms in l, calling f once there is fewer
    than k terms not assigned in l. [name] should be a registered extension, and together with
    the ordered list [l], it is used as a key to prevent duplicates watches.
    @param formula attach the watcher to a formula, so that the callback will only be called
      if the given formula is among the current assumption when the watcher triggers (i.e if the formula is true). *)

val model : unit -> (Expr.term * Expr.term) list
(** Returns the full assignment in the current model. *)

