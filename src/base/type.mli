
(** Transform Ast.term into Expr.formula.
    This module provides functions to parse terms from the untyped syntax tree
    defined in Ast, and generate formulas as defined in the Expr module. *)

exception Typing_error of string * Ast.term

type builtin_symbols = string -> Expr.ty list -> Expr.term list ->
  [ `Ty of Expr.ttype Expr.function_descr Expr.id  * Expr.ty list |
    `Term of Expr.ty Expr.function_descr Expr.id * Expr.ty list * Expr.term list ] option
(** The type of builtin symbols parser. Takes the name of the symbol and the number
    of arguments applied to it, and can return a type constructor or a term constant. *)

val new_type_def : Ast.symbol * int -> unit
(** Register a new type constructor. Takes the name of the constructor and its arity,
    and adds them to the global environment for type-checking. *)

val new_const_def : builtin_symbols -> Ast.symbol * Ast.term -> unit
(** Register a new constant. Take the name of the constant and a term representing
    its type, and adds it to the global environment for type-checking. *)

val parse : goal:bool -> builtin_symbols -> Ast.term -> Expr.Formula.t
(** Parse an input formula. The [~goal] argument states wether the formula
    is a goal or not (changes the status of the output formula). *)

