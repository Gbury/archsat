
(** Extension for rewriting *)

(** {2 Matching modulo equality} *)

val match_modulo : Expr.term -> Ext_eq.t -> Match.t Sequence.t
(** Matching modulo the equivalence classes registered in [Ext_eq]. *)

(** {2 Plugin} *)

val register : unit -> unit
(** Register the extension. *)

