

val stack : Backtrack.Stack.t

val add_type : Ast.symbol * Ast.term -> unit

val add_alias : Ast.symbol * Ast.term list * Ast.term -> unit

val parse : Ast.term -> Expr.Formula.t

