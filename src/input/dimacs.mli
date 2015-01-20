
exception Parse_error of int

val parse_file : string -> Expr.formula list list
