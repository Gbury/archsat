(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Module for Input/Output operations *)

(** {2 Printing wrappers} *)

(** Wrapper to output correct messages according to the output
    format's specification. *)

val prelude         : Options.opts -> string
(** Prelude to print before the interactive prompt. *)

val print_sat       : Format.formatter -> Options.opts -> unit
val print_unsat     : Format.formatter -> Options.opts -> unit
val print_unknown   : Format.formatter -> Options.opts -> unit
(** Prints a result on the formatter according to the output format set. *)

val print_exn       : Options.opts -> Format.formatter -> exn -> unit
(** Print the given error format string ot output. *)

