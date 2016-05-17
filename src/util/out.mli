
(** Module for Input/Output operations *)

(** {2 IO Wrappers} *)

val curr_output : unit -> Options.output
(* Current values for input/output format *)

val set_output : Options.output -> unit
val set_input_file : string -> unit
(** Sets the input, output, or input file to the given value. *)

(** {2 Printing wrappers} *)

(** Wrapper around Format.fprintf to print inside comments according to the output format. *)

val set_start : unit -> unit
(** Sets the starting time for printing the next result *)

val print_sat : Format.formatter -> unit
val print_unsat : Format.formatter -> unit
val print_unknown : Format.formatter -> unit
val print_timeout : Format.formatter -> unit
val print_spaceout : Format.formatter -> unit
(** Prints the resulton the formatter according to the output format set. *)

val print_error : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Print the given error format string ot output. *)

