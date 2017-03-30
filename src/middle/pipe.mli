
(** Top-level operations

    This module defines top-level operators, i.e functions to act
    on top-level statements. *)

(** {2 Types} *)

type type_decls = [
  | `Type_decl of Expr.ttype Expr.function_descr Expr.id
  | `Term_decl of Expr.ty Expr.function_descr Expr.id
]
(** The type of top-level type declarations. *)

type type_defs = [
  | `Type_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty
  | `Term_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty Expr.id list * Expr.term
]
(** The type of top-level type definitions. *)

type assume = [
  | `Hyp of Expr.formula
  | `Goal of Expr.formula
]
(** The type of top-level assertion statements *)

type solve = [
  | `Solve
]
(** Top-level solve instruction *)

type result = [
  | `Unknown
  | `Proof of Solver.proof
  | `Model of Solver.model
]
(** The type of results for a solve instruction. *)

type typechecked = [ type_defs | type_decls | assume | solve ]
(** The type of statements after typechecking *)

type solved      = [ type_defs | type_decls | assume | result ]
(** The type of solved statement *)

type +'a stmt = {
  impl_types : Expr.ttype Expr.function_descr Expr.id list;
  impl_terms : Expr.ty Expr.function_descr Expr.id list;
  contents  : 'a;
}
(** Wrapper around statements. It records implicit type declarations. *)

(** {2 Pipes} *)

val parse : Options.opts -> Options.opts * (Options.opts -> Dolmen.Statement.t option)
(** Parsing function. Reads the input options and returns a tuple of the new options
    (including the detected input language), togethter with a statement generator. *)

val execute : Options.opts * Dolmen.Statement.t -> Options.opts * Dolmen.Statement.t
(** Perform side effects of statement (such as the 'exit' statement. *)

val expand : Options.opts * Dolmen.Statement.t ->
  Options.opts * [ `Ok | `Gen of bool * Dolmen.Statement.t Gen.gen ]
(** Expand statements (such as includes). Returns the new options, and either:
    - [ `Ok ], which means the statement can be propagated as is
    - [ `Gen (flat, g) ], if the statement expands into a generator [g]. The bool [flat]
      indicates wether the statements in [g] should be treated as a single group of
      statements (with regards to timeouts, etc...), or as a list of independant statements
      (each with its own timeout...).
*)

val typecheck : Options.opts * Dolmen.Statement.t -> typechecked stmt
(** Typechecks a statement. *)

val solve : Options.opts * typechecked stmt -> solved stmt
(** Solve a statement *)

val print_res : Options.opts * solved stmt -> unit
(** Print the results of solved statements *)

val export : Options.opts * solved stmt -> unit
(** Export various information; usually for debugging purposes. *)

val print_proof : Options.opts * solved stmt -> unit
(** Print the proof according to the options *)


