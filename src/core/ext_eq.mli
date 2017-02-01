
(** Extension for equality *)

(** {2 Equivalence classes} *)

module Class : sig

  type t
  (** The type representing equality classes.
      NOTE: equality classes are immutable, and so the information they
          contain is only valid right after they are provided. *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual functions *)

  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
  (** Print a class. *)

  val find : Expr.term -> t
  (** Find the equality class of a term. *)

  val repr : t -> Expr.term
  (** Return the current representant of an equality class. *)

  val mem : t -> Expr.term -> bool
  (** Does a term belong to an equialence class. *)

  val fold : ('a -> Expr.term -> 'a) -> 'a -> t -> 'a
  (** Fold over the terms in an equivalence class. *)

  val find_top : t -> Expr.ty Expr.function_descr Expr.id -> Expr.term list
  (** Find all terms in an equivalence class that have the given function
      symbol at the top. *)

end

(** {2 Union-find callbacks} *)

val register_callback : string -> (Class.t -> Class.t -> Class.t -> unit) -> unit
(** [register_callback name f] registers the callback [f] to be called
    on each merge of two union-find equivalence classes. [name] should be
    the name of a registered extension, and [f] will only be called if
    the named extension is active. *)

(** {2 Plugin functions} *)

val assume : Expr.formula -> unit
(** Assume a new formula. *)

val eval_pred : Expr.formula -> (bool * Expr.term list) option
(** Evaluate a predicate. *)

val register : unit -> unit
(** Register the extension *)

