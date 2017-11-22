
(** Proof utilities

    Provides various utilities for proof output.
*)

val section : Section.t
(** Root debug section for proofs *)

(** {2 Local environments} *)

module Env : sig

  exception Added_twice of Term.t
  exception Not_introduced of Term.t

  type t
  (** The type of environments, i.e bijective maps
      between proof terms and names. *)

  val empty : t
  (** The empty environment. *)

  val prefix : t -> string -> t
  (** Change the prefix of the environment. THe prefix is used
      when introducing new formulas. *)

  val mem : t -> Term.t -> bool
  (** Does the Term belong to the environment ? *)

  val find : t -> Term.t -> Term.id
  (** Find the id associetd with a given term [t]. The returned id
      has type [t].
      @raise Not_introduced if term was not found *)

  val intro : t -> Term.t -> t
  (** Introduce the given term, automatically choosing a term for it,
      using the prefix of the environment. *)

end

(** {2 Proof prelude} *)

module Prelude : sig

  include Sig.Full
  (** Standard signature *)

  val require : ?deps:t list -> unit Expr.id -> t
  (** Require the given module (as an identifier). *)

  val alias : ?deps:t list -> Term.id -> Term.t -> t
  (** Make an alias for readability purposes. *)

  val topo : t list -> (t -> unit) -> unit
  (** [topo l iter] applies iter to every prelude in the
      reflexive transitive closure of dependencies of [l],
      such that [iter] is called on all dependencies of a prelude [p]
      before being called on [p]. *)

end


(** {2 Languages & printing} *)

type lang =
  | Coq     (** The Coq language *)
(** Supported languages for proof output (not to be confused with
    proof term output). *)

type pretty =
  | Branching           (** All branches are equivalent *)
  | Last_but_not_least  (** The last "branch" s the most important
                            and/or bigger one. *)
(** Pretty printing information about branches of a proof. *)


(** {2 Proof Contexts} *)

type sequent
(** Proof context, represents a goal to prove given an environment. *)

val env : sequent -> Env.t
val goal : sequent -> Term.t
(** Accessors for the environment and the goal of a context. *)

val mk_sequent : Env.t -> Term.t -> sequent
(** Make a context from environment and goal. *)



(** {2 Proofs objects} *)

type proof
(** The type of proof objects. A proof is created incomplete,
    and can then be compelted in a mutable way by applying
    reasoning steps to positions. *)

type pos
(** The type of positions within the proof. *)

val mk : sequent -> proof * pos
(** Create an empty proof with the given goal and environent.
    Returns the proof, together with the open position at the root
    of the proof. *)

val print : lang:lang -> Format.formatter -> proof -> unit
(** Print the proof in the given language. *)

val elaborate : proof -> Term.t
(** Elaborate the given proof into a proof term. *)



(** {2 Proof steps} *)

exception Failure of string * sequent
(** Exception designed to be raised by steps that fail. *)

type ('input, 'state) step
(** The type of reasonning steps. A reasonning step's goal is to
    take an context, and return a set of contexts, each corresponding
    to a branch that needs to be proven, much like in sequent calculus. *)

val mk_step :
  ?prelude:('state -> Prelude.t list) ->
  coq:pretty * (Format.formatter -> 'state -> unit) ->
  compute:(sequent -> 'input -> 'state * sequent array) ->
  elaborate:('state -> Term.t array -> Term.t) ->
  ('input, 'state) step
(** Create a reasoning step with internal state type ['state].
    The coq parameter is there for languages-specific printing.
    The compute function goal is to compute the branches
    to prove after application of th reasonning step.
    The elaboration function should compute the corresponding proof term.
    *)

val apply_step : pos -> ('a, 'b) step -> 'a -> 'b * pos array
(** Apply a reasoning step at a position in the proof. Returns the computed
    internal state, as well as  an array of positions corresponding to the
    branches to prove. These positions are in the same order as the branches
    computed by the reasoning step. *)


(** {2 Proof inspection} *)

type node
(** The type of internal node of proof trees *)

val root : proof -> node
(** Returns the root of a proof
    @raise Open_proof if there is no step applied to the root of the proof. *)

val branches : node -> node array
(** Returns the branches of a node.
    @raise Open_proof if there is at least one open branch. *)


