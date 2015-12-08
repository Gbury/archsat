
(** Extension to generate meta-variables *)

(** {2 Metavariables helpers}*)

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
}
(** A type to separate formulas in order to facilitate unification *)

val parse_slice : ((Expr.formula -> unit) -> unit) -> state
(** Create a slice from the iterator on formulas *)

val debug_st : int -> state -> unit
(** Output some debug info on the output *)

(** {2 Extension Options} *)

(** {3 Meta variable generation] *)

val meta_start : int ref
(** Number of meta to generate onthe first try *)

val meta_incr : bool ref
(** Sets wether new meta should be generated at each round *)

val meta_delay : (int * int) ref
(** Delay for new metavarsinstantiations *)

val meta_max : int ref
(** Max number of metas to generate for each formulas *)

