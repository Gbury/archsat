(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Typechecking of terms from Dolmen.Term.t
    This module provides functions to parse terms from the untyped syntax tree
    defined in Dolmen, and generate formulas as defined in the Expr module. *)

val section : Section.t
(** Debug section used in typechecking. *)

val stack : Backtrack.Stack.t
(** The undo stack used for storing globals during typechecking. *)

(** {2 Type definitions} *)

type env
(** The type of environments for typechecking. *)

exception Typing_error of string * env * Dolmen.Term.t
(** Exception raised when a typing error is encountered. *)

type expect =
  | Nothing
  | Type
  | Typed of Expr.ty
(** The type of expected result when typing an expression, used to infer
    non-declared symbols. *)

type tag = Any : 'a Tag.t * 'a -> tag
(** Existencial wrapper around tags *)

type res =
  | Ttype   : res
  | Ty      : Expr.ty -> res
  | Term    : Expr.term -> res
  | Formula : Expr.formula -> res
  | Tags    : tag list -> res (**)
(** The results of parsing an untyped term. *)

type inferred =
  | Ty_fun of Expr.Id.TyCstr.t
  | Term_fun of Expr.Id.Const.t
(** The type for inferred symbols. *)

type 'a typer = env -> Dolmen.Term.t -> 'a
(** A general type for typers. Takes a local environment and the current untyped term,
    and return a value. The typer may need additional information for parsing,
    in which case the return value will be a function. *)

type symbol =
  | Id of Dolmen.Id.t
  | Builtin of Dolmen.Term.builtin
(** Wrapper around potential function symbols from the Dolmen AST. *)

type builtin_symbols = (symbol -> Dolmen.Term.t list -> res option) typer
(** The type of a typer for builtin symbols. Takes the name of the symbol and the arguments
    applied to it, and can return a typechecking result.
    Can be useful for extensions to define overloaded operators such as addition in arithmetic,
    since the exact function symbol returned can depend on the arguments (or even be different
    between two calls with the same arguments). *)

(** {2 Environments} *)

val empty_env :
  ?expect:expect ->
  ?status:Expr.status ->
  ?infer_hook:(env -> inferred -> unit) ->
  ?explain:[ `No | `Yes | `Full ] ->
  builtin_symbols -> env
(** Create a new environment. *)

val expect : ?force:bool -> env -> expect -> env
(** Returns the same environment but with the given expectation,
    except if the environnement already except [Nothing]. *)

val find_var : env -> Dolmen.Id.t ->
  [ `Not_found
  | `Ty of Expr.ttype Expr.id
  | `Term of Expr.ty Expr.id ]
(** Lookup a variable in an environment. *)

(** {2 Parsing helpers} *)

val wildcard : (Dolmen.Id.t -> Dolmen.Term.t list -> res) typer
(** Parse a term as a wildcard (only allowed in types).
    Accepts as argument the list of arguments given to the widcard symbol in the
    Dolmen AST. If that list if non_empty, an expcetion is raised.
    *)

val ty_apply :
  (Expr.Id.TyCstr.t -> Expr.ty list -> Expr.ty) typer
val term_apply :
  (Expr.Id.Const.t -> Expr.ty list -> Expr.term list -> Expr.term) typer
(** Wrappers for making applications, so that it raises the right exceptions. *)

(** {2 Parsing functions} *)

val parse_expr : res typer
(** Main parsing function. *)

val parse_ty : Expr.ty typer
val parse_term : Expr.term typer
val parse_formula : Expr.formula typer
(** Wrappers around {parse_expr} to unwrap an expected result. *)

val parse_app_ty : (Expr.Id.TyCstr.t -> Dolmen.Term.t list -> res) typer
val parse_app_term : (Expr.Id.Const.t -> Dolmen.Term.t list -> res) typer
(** Function used for parsing applications. The first dolmen term given
    is the application term being parsed (used for reporting errors). *)

val parse_app_formula : (Expr.formula -> Dolmen.Term.t list -> res) typer
(** Aply a formula to a list of terms. Will raise an error if the list is not
    empty. Useful during parsing of formulas constants such as [true] or [false]. *)

(** {2 High-level functions} *)

val new_decl :
  (?attr:Dolmen.Term.t -> Dolmen.Id.t ->
   [ `Type_decl of Expr.Id.TyCstr.t
   | `Term_decl of Expr.Id.Const.t
   ]) typer
(** Parse a declaration. *)

val new_def :
  (?attr:Dolmen.Term.t -> Dolmen.Id.t ->
   [ `Type_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty
   | `Term_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty Expr.id list * Expr.term
   ]) typer
(** Parse a definition *)

val new_formula : Expr.formula typer
(** Parse a formula *)

