
(** Module for Input/Output operations *)

exception Parsing_error of ParseLocation.t * string
(** Syntax error with loaction and error message. *)

(** {2 IO Wrappers} *)

val set_input : Options.input -> unit
val set_output : Options.output -> unit
val set_input_file : string -> unit
(** Sets the input, output, or input file to the given value. *)

val parse_input : string -> Ast.command Queue.t
(** Parse the given input file according to the current input options.
    @raise Parsing_error if there is there is an error while parsing the given file. *)

val input_env : unit -> Type.builtin_symbols
(** Return the builtin symbols for the current input format. *)

(** {2 Printing wrappers} *)

(** Wrapper around Format.fprintf to print inside comments according to the output format. *)

val print_sat : Format.formatter -> unit
val print_unsat : Format.formatter -> unit
val print_timeout : Format.formatter -> unit
val print_spaceout : Format.formatter -> unit
(** Prints the resulton the formatter according to the output format set. *)

val print_error : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Print the given error format string ot output. *)

val print_model : Format.formatter -> (Expr.term * Expr.term) list -> unit
(** Prints the assignemnts in the model, one by line. *)

val print_proof : (Format.formatter -> Solver.proof -> unit) ->
  Format.formatter -> Solver.proof -> unit
(** Wrapper around a proof printer. *)

