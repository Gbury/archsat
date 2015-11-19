
(* Type definitions *)
(* ************************************************************************ *)

exception Lexing_error of ParseLocation.t
exception Parsing_error of ParseLocation.t * string


(* Some utilities *)
(* ************************************************************************ *)

let rec consume_line lexbuf =
  match Lex.token lexbuf with
  | Lex.CHAR '\n' -> Lexing.new_line lexbuf
  | _ -> consume_line lexbuf

