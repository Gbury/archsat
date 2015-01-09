
(** Plugin Manager *)

include Msat.Plugin_intf.S
  with type term = Expr.term and type formula = Expr.formula
(** This module is a valid Plugin for Mcsat *)



(** {2 Exceptions} *)

exception Not_assigned of term
(** The given term does not have a current assignment *)

exception Absurd of formula list
(** To be used by extensions in their 'assume' function *)

exception Extension_not_found of string
(** Raised by activate *)



(** {2 Extension Registering} *)

type term_eval =
  | Interpreted of term * int
  | Waiting of term

type extension = {
  name : string;
  assume : slice -> unit;
  assign : term -> term option;
  eval_term : term -> term_eval;
  eval_pred : term -> (bool * int) option;
  interprets : Expr.ty Expr.function_descr Expr.var -> bool;
  backtrack : int -> unit;
  current_level : unit -> int;
}
(** Type of plugins/extensions *)

val register : extension -> unit
(** Used in extensions files to register extensions. *)

val activate : string -> unit
(** Used in order to make one of the extensions registered previously active, i.e
    use the functions provided by the extension. *)

val list_extensions : unit -> string list
(** Returns the current list of extensions known to the dispatcher. *)



(** {2 Assignment functions} *)

val get_assign : term -> term * int
(** [get_assign t] Returns the current assignment of [t] and its level, if it exists.
    @raise Not_assigned if the term isn't assigned *)

val set_assign : term -> term -> int -> unit
(** [set_assign t v lvl] sets the assignment of [t] to [v], with level [lvl].
    May erase previous assignment of [t]. *)

val try_eval : term -> term option
(** Try and eval the given term. In case it fails, sets up a watching scheme to
    evaluate as soon as possible. *)

val watch : term -> (term * term -> unit) -> unit
(** Set a callback function to be called once the given term has been evaluated. The callback function is called
    with the pair term, assigned value. *)

val model : unit -> (term * term) list
(** Returns the fulla ssignment in the current model. *)
