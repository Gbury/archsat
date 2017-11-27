
(** Rwrite rules

    This module sdefines types and manipulation functions on rerite rules.
*)

(** {2 Rewrite rule guards} *)

module Guard : sig

  type t =
    | Pred_true of Expr.term
    | Pred_false of Expr.term
    | Eq of Expr.term * Expr.term

  val map : (Expr.term -> Expr.term) -> t -> t
  (** Map a function on the terms in a guard. *)

  val to_list : t -> Expr.term list
  (** Returns the list of all top-level terms appearing in a guard. *)

  val check : t -> bool
  (** Check wether a guard is verified. *)

end

(** {2 Rewrite rule triggers} *)

module Trigger : sig

  type t =
    | Single of Expr.term
    | Equal of Expr.term * Expr.term

end

(** {2 Rewrite rules} *)

module Rule : sig

  type result =
    | Term of Expr.term
    | Formula of Expr.formula

  type t = private {
    id       : int;
    manual   : bool;
    trigger  : Trigger.t;
    result   : result;
    guards   : Guard.t list;
    formula  : Expr.formula;
  }
  (** A rewrite rule *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual functions *)

  val print :
    ?term:Expr.term CCFormat.printer ->
    ?formula:Expr.formula CCFormat.printer ->
    t CCFormat.printer
  (** A modular printer. *)

  val print_id : t CCFormat.printer
  (** Print only the rule id (shorter). *)

  val mk : ?guards:Guard.t list -> bool -> Trigger.t -> result -> t
  (** [mk ?guards is_manual trigger result] creates a new rewrite rule, with
      the formula field set to the constant [true] formula. *)

  val add_guards : Guard.t list -> t -> t
  (** Add the guards to the rule, in no specified order. *)

  val set_formula : Expr.formula -> t -> t
  (** Set the top-level formula of the rewrite rule. *)

  val is_manual : t -> bool
  (** Returns wether the rule is a manual one. *)

end

(** {2 Term normalization} *)

module Normalize : sig

  type finder =
    Rule.t list -> Expr.term ->
    (Rule.t * Expr.term * Position.t) option
  (** A finder function's goal is to find the next occurence of a rewrit rule
      to apply when trying to normalize a term. It shoudl return a triplet
      containing: the rule used, the result of the rule, and the position
      where to substitutite the given result. *)

  val top_down : finder
  (** A finder that first looks atthe root of the term, then descends in
      a top-down fashion. *)

  val normalize :
    find:finder -> Rule.t list -> Expr.term -> Rule.t list * Expr.term
  (** Using the given finder function, returns the normalized term, along with the
      list of all rules that were used to normalize the term. *)


end
