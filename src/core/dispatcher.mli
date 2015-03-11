
(** Plugin Manager *)

type id

type lemma = private {
  proof_ext : id;
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

exception Extension_not_found of string
(** Raised by activate *)

(** {2 Command line options} *)

val add_opts : Options.copts Cmdliner.Term.t -> Options.copts Cmdliner.Term.t
(** Returnsa term with added command line options from extensions. *)

(** {2 Proof management} *)

val mk_proof : ?ty_args : Expr.ty list ->
               ?term_args : Expr.term list ->
               ?formula_args : Expr.formula list ->
               id -> string -> proof
(** Returns the associated proof. Optional arguments not specified are assumed ot be empty lists. *)

(** {2 Extension Registering} *)

type extension = {
  id : id;
  name : string;
  descr : string;
  if_sat : unit -> unit;
  assume : formula * int -> unit;
  eval_pred : formula -> (bool * int) option;
  preprocess : formula -> unit;
  options : Options.copts Cmdliner.Term.t -> Options.copts Cmdliner.Term.t;
}
(** Type of plugins/extensions *)

val new_id : unit -> id
(** Generates a new, unique extension id. *)

val register : extension -> unit
(** Used in extensions files to register extensions. *)

val activate : string -> unit
(** Used in order to make one of the extensions registered previously active, i.e
    use the functions provided by the extension. *)

val deactivate : string -> unit
(** Used in order to undo the activation of one of the extensions, i.e
    stop using the functions provided by the extension. *)

val set_ext : string -> unit
(** With argument "-ext_name", deactivates the extension, else activates it. *)

val set_exts : string -> unit
(** Same as set_ext but considers a comma-separated list of arguments. *)

val list_extensions : unit -> string list
(** Returns the current list of extensions known to the dispatcher. *)

val ext_doc : unit -> Cmdliner.Manpage.block list
(** Returns a documentation on available options. *)

(** {2 Extension-side helpers} *)

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

(*
val try_eval : term -> term option
(** Try and eval the given term. In case it fails (and returns [None]),
    it sets up a watching scheme to evaluate the given term as soon as possible. *)
*)

val watch : id -> int -> term list -> (unit -> unit) -> unit
(** [watch tag k l f] sets up a k-watching among the terms in l, calling f once there is less
    then k terms not assigned in l. The pair [(l, tag)] is used as a key to eliminate duplicates. *)

val model : unit -> (term * term) list
(** Returns the full assignment in the current model. *)

