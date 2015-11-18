
(** Module forsome helpers during lexing/parsing *)

(** {2 Exceptions} *)

exception Lexing_error of ParseLocation.t
(** Lexing error: invalid character *)

exception Parsing_error of ParseLocation.t * string
(** Syntax error with loaction and error message. *)

(** {2 Helpers} *)

val consume_line : Lexing.lexbuf -> unit
(** Consume all characters on of the buffer until a newline character is found. *)

