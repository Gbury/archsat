
(** Module for Input/Output operations *)

val set_input : string -> unit
val set_output : string -> unit
(** Sets the input or output to the given format.
    @raise Invalid_argument if the string is not recognised *)

exception Syntax_error of int * int * string
(** Syntax error with : line number, character number, error message. *)

val parse_input : string -> Expr.formula list list
(** Parse the given input file according to the current input options.
    @raise Syntax_error if there is a syntax error in the given file. *)

val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Wrapper around Format.fprintf to print inside comments according to the output format. *)

val print_model : Format.formatter -> (Expr.term * Expr.term) list -> unit
(** Prints the assignemnts in the model, one by line. *)

