(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(**
   mSAT solver instanciated with Dispatcher Plugin.
   See {{: https://github.com/Gbury/mSAT} mSAT}
   for more information on mSAT.
*)


(** {2 Proofs & Models} *)

module Proof : Msat.Res.S with module St = Dispatcher.SolverTypes
(** Msat proof module *)

module Model : sig
  (** Model manipulations. *)

  type t
  (** The type of models *)

  val print : Format.formatter -> t -> unit
  (** Print a model on the given formatter. *)

end


(** {2 Type defs} *)

type id
(** Abstract type for hypothesis identifiers. *)

type model = Model.t
(** The type of models. *)

type proof = Proof.proof
(** The type of proofs. *)

type view = (Expr.formula -> unit) -> unit
(** A view of the trail when the solver has reached SAT *)

type res =
  | Sat of model
  | Unsat of proof
  | Unknown
(** Type of results returned by the solver *)


(** {2 Core solver} *)

val section : Section.t
(** Main section for solving. *)

val assume : solve:bool -> Expr.formula list -> id
(** Add a clause to the current problem, and return the corresponding proof id.
    @solve determine wether to really add the clause to the solver, else
           just the proof id is generated. *)

val solve :
  ?check_model:bool ->
  ?check_proof:bool ->
  ?export:Format.formatter ->
  ?assumptions:Expr.formula list ->
  unit -> res
(** Try and solve the current set of assumptions.
    @param export output an iCNF problem file equivalent to
        the solved problems on the formatter.
    @param check_model if [true] then checks every model that
        the SAT solver outputs (using mSAT internal functions).
    @param check_proof if [true] then checks every proof that
        the SAT solver outputs (using mSAT internal functions).
*)

val add_atom : Expr.formula -> unit
(** Add the given formula to the sat-solver to ensure
    it is decided on (along with its subterms). *)

val export_dimacs : Format.formatter -> unit -> unit
(** Export the current problem in dimacs format. *)

val register_hyp : id -> Term.id -> unit
(** Assign the given proof id to the hyp linked to the identifier. *)

val register_goal : id -> Term.id -> unit
(** Assign the given proof id to the hyp linked to the identifier. *)

val is_registered : Dispatcher.SolverTypes.clause -> bool
(** is the clause registered as a hypothesis (else, it should be a goal). *)

val hyp_proof : Dispatcher.SolverTypes.clause -> Term.id
(** Get the proof id of an hypothesis clause. *)


(** {2 Dispatcher messages} *)

type unsat_ret =
  | Unsat_ok

type sat_ret =
  | Sat_ok
  | Restart
  | Incomplete
  | Assume of Expr.formula list

type _ Dispatcher.msg +=
  | Restarting : unit Dispatcher.msg
  | Found_sat : view -> sat_ret Dispatcher.msg
  | Found_unsat : proof -> unsat_ret Dispatcher.msg
  | Found_unknown : unit -> unit Dispatcher.msg
(** Dispatcher messages. *)


