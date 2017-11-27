
(** Extension for rewriting *)

(** {2 Matching modulo equality} *)

val match_modulo : Expr.term -> Ext_eq.Class.t -> Mapping.t list
(** Matching modulo the equivalence classes registered in [Ext_eq]. *)

(** {2 Plugin} *)

val tag : bool Expr.tag
(** Formulas that have been understood as rewrite rules are marked using
    this tag set ot true. *)

val register : unit -> unit
(** Register the extension. *)

