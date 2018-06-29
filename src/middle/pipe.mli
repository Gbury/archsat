
(** Top-level operations

    This module defines top-level operators, i.e functions to act
    on top-level statements. *)

(** {2 Types} *)

type 'a tr_stmt = {
  contents : 'a;
  implicit : Term.id list;
}
(* Used for wrapping translated contents with implicit declarations *)

type +'a stmt = {
  id          : Dolmen.Id.t;
  contents    : 'a;
  loc         : Dolmen.ParseLocation.t option;
}
(** Wrapper around statements. It records implicit type declarations. *)

type executed = [
  | `Executed
]

type type_decls = [
  | `Type_decl of Expr.Id.TyCstr.t
  | `Term_decl of Expr.Id.Const.t
]
(** The type of top-level type declarations. *)

type decl = [
  `Decl of Term.id tr_stmt
]
(** The type of proof id declaration. *)

type type_defs = [
  | `Type_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty
  | `Term_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty Expr.id list * Expr.term
]
(** The type of top-level type definitions. *)

type def = [
  | `Def of (Dolmen.Id.t * Term.t) tr_stmt
]
(** The type of id definition. *)

type assume = [
  | `Hyp of Expr.formula
  | `Goal of Expr.formula
  | `Clause of Expr.formula list
]
(** The type of top-level assertion statements *)

type solve_sequent = [
  | `Left of Solver.id * Expr.formula
  | `Right of Solver.id * Expr.formula
]
(** The type of sequent components (for proof output). *)

type proof_sequent = [
  | `Left of Term.id tr_stmt
  | `Right of (Solver.id * Term.id) tr_stmt
]

type solve = [
  | `Solve
]
(** Top-level solve instruction *)

type result = [
  | `Skipped
  | `Unknown
  | `Proof of Solver.proof
  | `Model of Solver.model
]
(** The type of results for a solve instruction. *)

type typechecked = [ executed | type_defs | type_decls | assume | solve ]
(** The type of statements after typechecking *)

type solved      = [ executed | type_defs | type_decls | solve_sequent | result ]
(** The type of solved statement *)

type translated  = [ executed | decl | def | proof_sequent | result ]
(** The type of translated statements *)


(** {2 Pipes} *)

val parse : Options.opts -> Options.opts * (Options.opts -> Dolmen.Statement.t option)
(** Parsing function. Reads the input options and returns a tuple of the new options
    (including the detected input language), togethter with a statement generator. *)

val execute : Options.opts * Dolmen.Statement.t ->
  [ `Continue of Options.opts * Dolmen.Statement.t | `Done of Options.opts ]
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

val run_typecheck : Options.opts -> bool
(** Should the typechecker be run ? *)

val typecheck : Options.opts * Dolmen.Statement.t -> typechecked stmt
(** Typechecks a statement. *)

val solve : Options.opts * typechecked stmt -> solved stmt
(** Solve a statement *)

val print_res : Options.opts * solved stmt -> unit
(** Print the results of solved statements *)

val translate : Options.opts * solved stmt -> translated stmt
(** Translate statements into proof statements *)

val export : Options.opts * translated stmt -> unit
(** Export various information; usually for debugging purposes. *)

val print_proof : Options.opts * translated stmt -> unit
(** Print the proof according to the options *)

val print_model : Options.opts * translated stmt -> unit
(** Print the proof according to the options *)

