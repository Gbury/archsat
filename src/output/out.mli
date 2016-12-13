
(** Module for Input/Output operations *)

(** {2 Printing wrappers} *)

(** Wrapper to output correct messages according to the output
    format's specification. *)

val prelude         : Options.copts -> string
(** Prelude to print before the interactive prompt. *)

val print_sat       : Options.copts -> unit
val print_unsat     : Options.copts -> unit
val print_unknown   : Options.copts -> unit
(** Prints the resulton the formatter according to the output format set. *)

val print_exn       : Options.copts -> exn -> unit
(** Print the given error format string ot output. *)

