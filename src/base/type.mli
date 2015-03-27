


val new_type_def : Ast.symbol * int -> unit
val new_const_def : Ast.symbol * Ast.term -> unit

val parse : bool -> Ast.term -> Expr.Formula.t

