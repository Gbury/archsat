
exception Parse_error of ParseLocation.t * string

val parse_file : string -> Ast.command Queue.t

