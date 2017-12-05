
(** Extension to generate meta-variables *)

(** {2 Metavariables helpers} *)

val iter : (Expr.formula -> unit) -> unit
(** Iter over all formulas that potentially generate metas *)

val do_formula : Expr.formula -> unit
(** Generate a meta variable associated with the given formula, and push
    the corresponding instantiation clause ot the solver.
    Does nothing on formulas which cannot generate meta-variables. *)

(** {2 Parsgin input formulas} *)

type state = {
  mutable true_preds : Expr.term list;
  mutable false_preds : Expr.term list;
  mutable equalities : (Expr.term * Expr.term) list;
  mutable inequalities : (Expr.term * Expr.term) list;
  mutable formulas : Expr.formula list;
}
(** A type to separate formulas in order to facilitate unification *)

val empty_st : unit -> state
(** Returns a fresh empty state *)

val parse_aux : state -> Expr.formula -> unit
(** Modifies state in place to add the terms in the given formula *)

val parse_slice : ((Expr.formula -> unit) -> unit) -> state
(** Create a slice from the iterator on formulas *)

val print : Format.formatter -> state -> unit
(** Output some debug info on the output *)

val fold_diff : ('a -> Expr.term -> Expr.term -> 'a) -> 'a -> state -> 'a
(** Fold over all terms that should be different in the state, i.e
    all pair of terms [(a, b)], such that either [a <> b] is a disequality in
    the state, or [a] is a true predicate, and [b] a false one. *)

(** {2 Extension Options} *)

(** {3 Meta variable generation} *)

val meta_start : int ref
(** Number of meta to generate on the first try *)

val meta_incr : bool ref
(** Sets wether new meta should be generated at each round *)

val meta_delay : (int * int) ref
(** Delay for new metavarsinstantiations *)

val meta_max : int ref
(** Max number of metas to generate for each formulas *)

(** {2 Plugin} *)

val register : unit -> unit
(** Register the extension. *)

