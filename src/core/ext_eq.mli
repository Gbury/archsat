
(** Extension for equality *)

(** {2 Equivalence classes} *)

type t
(** The type representing equality classes.
    NOTE: equality classes are immutable, and so the information they
          contain is only valid right after they are provided. *)

val print : Format.formatter -> t -> unit
(** Print a class. *)

val find : Expr.term -> t
(** Find the equality class of a term. *)

val repr : t -> Expr.term
(** Return the current representant of an equality class. *)

val fold : ('a -> Expr.term -> 'a) -> 'a -> t -> 'a
(** Fold over the terms in an equivalence class. *)

val find_top : t -> Expr.ty Expr.function_descr Expr.id -> Expr.term list
(** Find all terms in an equivalence class that have the given function
    symbol at the top. *)

(** {2 Plugin functions} *)

val assume : Expr.formula -> unit
(** Assume a new formula. *)

val eval_pred : Expr.formula -> (bool * Expr.term list) option
(** Evaluate a predicate. *)

val register : unit -> unit
(** Register the extension *)

