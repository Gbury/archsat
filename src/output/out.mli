
(** Module for Input/Output operations *)

(** {2 Printing wrappers} *)

(** Wrapper to output correct messages according to the output
    format's specification. *)

val prelude         : Options.opts -> string
(** Prelude to print before the interactive prompt. *)

val print_sat       : Options.opts -> unit
val print_unsat     : Options.opts -> unit
val print_unknown   : Options.opts -> unit
(** Prints the resulton the formatter according to the output format set. *)

val print_exn       : Options.opts -> exn -> unit
(** Print the given error format string ot output. *)

