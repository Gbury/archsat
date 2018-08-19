
(** Rwrite rules

    This module sdefines types and manipulation functions on rerite rules.
*)

(** {2 Rewrite rule guards} *)

module Guard : sig

  type t =
    | Pred_true of Expr.term
    | Pred_false of Expr.term
    | Eq of Expr.term * Expr.term
    | Neq of Expr.term * Expr.term

  val print :
    ?term:(Format.formatter -> Expr.term -> unit) ->
    Format.formatter -> t -> unit
  (** Printer function for guards. *)

  val map : (Expr.term -> Expr.term) -> t -> t
  (** Map a function on the terms in a guard. *)

  val to_list : t -> Expr.term list
  (** Returns the list of all top-level terms appearing in a guard. *)

  val check : t -> bool
  (** Check wether a guard is verified. *)

end

(** {2 Rewrite rules} *)

module Rule : sig

  type 'a witness =
    | Term : Expr.term witness
    | Formula : Expr.formula witness

  type 'a rewrite = {
    trigger : 'a;
    result : 'a;
  }

  type contents = C : 'a witness * 'a rewrite -> contents

  type t = {
    id       : int;
    manual   : bool;
    formula  : Expr.formula;
    guards   : Guard.t list;
    contents : contents;
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

  val mk_term : ?guards:Guard.t list -> bool -> Expr.term -> Expr.term -> t
  val mk_formula : ?guards:Guard.t list -> bool -> Expr.formula -> Expr.formula -> t
  (** [mk ?guards is_manual trigger result] creates a new rewrite rule, with
      the formula field set to the constant [true] formula. *)

  val add_guards : Guard.t list -> t -> t
  (** Add the guards to the rule, in no specified order. *)

  val set_formula : Expr.formula -> t -> t
  (** Set the top-level formula of the rewrite rule. *)

  val is_manual : t -> bool
  (** Returns wether the rule is a manual one. *)

end

(** {2 Rewrite substitution} *)

module Subst : sig

  type t
  (** The type of a rewrite substitution. *)

  val print : Format.formatter -> t -> unit
  (** print a substitution *)

  val rule : t -> Rule.t
  (** Returns the rewrite rule used for the substitution *)

  val inst : t -> Mapping.t
  (** Returns the mappping used to instantiate the rule for the substitution *)

  val formula : t -> Expr.formula
  (** hortcut to directly extract the formula from the rewrite rule of the subst *)

  val info : t -> Rule.contents
  (** Returns the exact contents that have been substituted. *)

end

(** {2 Term normalization} *)

module Normalize : sig

  val normalize_term :
    Rule.t list -> Subst.t list -> Expr.term -> Expr.term * Subst.t list

  val normalize_atomic :
    Rule.t list -> Subst.t list -> Expr.formula -> Expr.formula * Subst.t list

end

(** {2 Narrowing} *)

module Narrow : sig

  val term : Expr.term -> Rule.t list -> (Rule.t * Mapping.t * Mapping.t) list
  val formula : Expr.formula -> Rule.t list -> (Rule.t * Mapping.t * Mapping.t) list
  (** Tries and narrow the given term/formula, and returns a list of triples
      (rule, rule_inst, meta_inst) that allows to unify with the term.
      Instances of simple rewrite rule (which require no meta instanciation), are
      stripped away from the list of returned results. Addtionally, each mapping
      may refer to some fresh variables. *)

end
