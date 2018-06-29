
(** Proof utilities

    Provides various utilities for proof output.
*)

val section : Section.t
(** Root debug section for proofs *)

(** {2 Local environments} *)

module Env : sig

  exception Not_introduced of Term.t
  exception Conflict of Term.id * Term.id

  type t
  (** The type of environments, i.e bijective maps
      between proof terms and names. *)

  val print : Format.formatter -> t -> unit
  (** Printing function to be used for debugging. *)

  val empty : t
  (** The empty environment. *)

  val exists : t -> Term.id -> bool
  (** Does the id belong to the environment ? *)

  val mem : t -> Term.t -> bool
  (** Does the term exists in the environment ? *)

  val find : t -> Term.t -> Term.id
  (** Find the id associetd with a given term [t]. The returned id
      has type [t].
      @raise Not_introduced if term was not found *)

  val intro : ?hide:bool -> t -> string -> Term.t -> Term.id * t
  (** Introduce the given term, automatically choosing a term for it,
      using the prefix of the environment. *)

  val add : t -> Term.id -> t
  (** Add the given identifier to the environment. *)

  val declare : t -> Term.id -> t
  (** Add the given global identifier to the environment. *)

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
  | Dot     (** The DOT graphviz language *)
  | Coq     (** The Coq language *)
(** Supported languages for proof output (not to be confused with
    proof term output). *)

type pretty =
  | Branching           (** All branches are equivalent *)
  | Last_but_not_least  (** The last "branch" is the most important
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
    and can then be completed in a mutable way by applying
    reasoning steps to positions. *)

type pos
(** The type of positions within the proof. *)

val mk : sequent -> proof
(** Create an empty proof with the given goal and environent. *)

val pp_pos : Format.formatter -> pos -> unit
(** Print a proof position. *)

val print : lang:lang -> Format.formatter -> proof -> unit
(** Print the proof in the given language. *)

val print_term : lang:lang -> Format.formatter -> proof -> unit
(** Print the proof term corresponding t the proof in the given language. *)

val elaborate : proof -> Term.t
(** Elaborate the given proof into a proof term. *)



(** {2 Proof steps} *)

exception Failure of string * pos
(** Exception designed to be raised by steps that fail. *)

type ('input, 'state) step
(** The type of reasonning steps. A reasonning step's goal is to
    take a context, and return a set of contexts, each corresponding
    to a branch that needs to be proven, much like in sequent calculus. *)

val mk_step :
  ?prelude:('state -> Prelude.t list) ->
  ?dot:pretty * (Format.formatter -> 'state -> unit) ->
  coq:pretty * (Format.formatter -> 'state -> unit) ->
  compute:(sequent -> 'input -> 'state * sequent array) ->
  elaborate:('state -> Term.t array -> Term.t) -> string ->
  ('input, 'state) step
(** Create a reasoning step with internal state type ['state].
    The non-named string argument is the name of the step.
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

val intro : (string, Term.id) step
(** The itnroduction reasoning step. *)

val apply : (Term.t * int * Prelude.t list,
             Term.t * int * Prelude.t list) step
(** The term application reasoning step. Aplplies the given term,
    using the integer provided as arity i.e the number of arguments
    expected by the term, and thus also of branhces generated. *)

val letin : (string * Term.t, Term.id * Term.t) step
(** Let-binding in proofs. Given a prefix string, and a term,
    generate a new id and bind it to the given term for the
    remainder of the proof. *)

val cut : (string * Term.t, Term.id) step
(** Cut/assertion in proofs. Generate two branch,
    the first one in which the given term has to be proven,
    and a second one where the proven term has been bound
    to the returned id. The first boolean parameter determines whether
    the current env should be kept when proving the given term. *)


(** {2 Proof inspection} *)

type node
(** The type of internal node of proof trees *)

type proof_node =
  | Open  : sequent -> proof_node
  | Proof : (_, 'state) step * 'state * node array -> proof_node

exception Open_proof
(** Exception raised during traversal if an incomplete proof is found. *)

val root : proof -> node
(** Returns the root of a proof
    @raise Open_proof if there is no step applied to the root of the proof. *)

val pos : node -> pos
(** Return the position of a node. *)

val get : pos -> node
(** Return a node given its position. *)

val extract : node -> proof_node
(** Extract the contents of a node. *)

val branches : node -> node array
(** Returns the branches of a node.
    @raise Open_proof if there is at least one open branch. *)


(** {2 Proof tactics and useful stuff} *)

type ('a, 'b) tactic = 'a -> 'b
(** The type of tactics. Should represent computations that manipulate
    proof positions. Using input ['a] and output ['b].

    Most proof tactics should take a [pos] as input, and return:
    - [unit] if it closes the branch
    - a single [pos] it it does not create multple branches
    - a tuple, list or array of [pos] if it branches
*)

type _ Dispatcher.msg +=
  | Lemma : Dispatcher.lemma_info -> (pos, unit) tactic Dispatcher.msg (**)
(** Dispatcher message for theories to return proofs. *)

val match_arrow : Term.t -> (Term.t * Term.t) option
(** Try ad match the given term with an arrow type, is succesful returns
    the pair (argument_type, return_type). *)

val match_arrows : Term.t -> Term.t list * Term.t
(** Try ad match the given term with an arrow type as much as possible,
    and return the list of argument types expected, followed by
    the return type of the function type provided. *)

