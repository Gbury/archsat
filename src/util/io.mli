
(** Module for Input/Output operations *)

exception Parsing_error of ParseLocation.t * string
(** Syntax error with loaction and error message. *)

exception Setting_not_found of string * string * string list
(** Raised by [set_input] and [set_output].
    The first argument if the name of the option, the second the argument used, and third
    the list of valid arguments. *)

(** {2 IO Wrappers} *)

val set_input : string -> unit
val set_output : string -> unit
(** Sets the input or output to the given format.
    @raise Setting_not_found if the string is not recognised *)

val parse_input : string -> Ast.command Queue.t
(** Parse the given input file according to the current input options.
    @raise Syntax_error if there is a syntax error in the given file. *)

(** {2 Printing wrappers} *)

val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Wrapper around Format.fprintf to print inside comments according to the output format. *)

val print_res : Format.formatter -> string -> float -> unit
(** Prints the string and float in current format. *)

val print_model : Format.formatter -> (Expr.term * Expr.term) list -> unit
(** Prints the assignemnts in the model, one by line. *)

val print_proof : Format.formatter -> Solver.proof -> unit
(** Prints the given proof according to the current output format. *)
