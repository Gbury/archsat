
exception Parse_error of int

val parse_file : string -> Ast.command Gen.t

