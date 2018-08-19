(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Extension for rewriting *)

(** {2 Plugin} *)

val tag : bool Expr.tag
(** Formulas that have been understood as rewrite rules are marked using
    this tag set ot true. *)

val normalized : bool Expr.tag
val normal_form : bool Expr.tag
(** Tag attached to normal forms/normalized formulas. *)

val get_active : unit -> Rewrite.Rule.t list
(** Get the current active rewrite rules. *)

val register : unit -> unit
(** Register the extension. *)

