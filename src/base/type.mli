
(** Typechecking of terms from Dolmen.Term.t
    This module provides functions to parse terms from the untyped syntax tree
    defined in Dolmen, and generate formulas as defined in the Expr module. *)

exception Typing_error of string * Dolmen.Term.t

val section : Util.Section.t
(** Debug section used in typechecking. *)

val stack : Backtrack.Stack.t
(** The undo stack used for storing globals during typechecking. *)

(** {2 Type definitions} *)

type env
(** The type of environments for typechecking. *)

type res =
  | Ttype
  | Ty of Expr.ty
  | Term of Expr.term
  | Formula of Expr.formula (**)
(* The results of parsing an untyped term.  *)

type builtin_symbols = env -> string -> Dolmen.Term.t list -> res option
(** The type of a parser for builtin symbols. Takes the name of the symbol and the arguments
    applied to it, and can return a typechecking result.
    Can be useful for extensions to define overloaded operators such as addition in arithmetic,
    since the exact function symbol returned can depend on the arguments (or even be different
    between two calls with the same arguments). *)

(** {2 Parsing} *)

val parse_expr : env -> Dolmen.Term.t -> res
(** Main parsing function. *)


(** {2 High-level functions} *)

val new_decl : builtin:builtin_symbols -> string -> Dolmen.Term.t -> unit

val new_def  : builtin:builtin_symbols -> string -> Dolmen.Term.t -> unit

