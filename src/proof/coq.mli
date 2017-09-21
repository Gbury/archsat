
(** Proof in the Coq format

    This module defines helprs for printing coq proof scripts
    corresponding to unsatisfiability proofs.
*)

(** {2 Types} *)

type prelude
(** Abstract type representing preludes, i.e. requirements
    for tactics. *)

type tactic
(** Abstract type repreenting tactics. *)

type 'a selector =
  | All
  | Mem of 'a list
  | Pred of ('a -> bool)
(** Type for selectors of value of type ['a]. *)

(** {2 Dispatcher messages} *)

type _ Dispatcher.msg +=
  | Tactic : Dispatcher.lemma_info -> tactic Dispatcher.msg (**)
(** Sent to the extension that produced a proof;
    asks for it to prove the clause/lemma it produced, using a coq tactics. *)

(** {2 Main} *)

val declare_ty : Format.formatter -> Expr.ttype Expr.function_descr Expr.id -> unit
val declare_term : Format.formatter -> Expr.ty Expr.function_descr Expr.id -> unit
(** Print the type declarations for constant symbols *)

val print_hyp : Format.formatter -> (Dolmen.Id.t * Expr.formula list) -> unit
(** Print an hypothesis/axiom *)

val print_proof : Format.formatter -> Solver.proof -> unit
(** Print a theorem, proving the named goals previously added using the given proof. *)


(** {2 Prelude} *)

module Prelude : sig

  type t = prelude
  (** Type alias *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual functions *)

  module S : Set.S with type elt = t
  (** Moduel to create sets of preludes *)

  val epsilon : t
  (** The prelude requiring the epsilon module, i.e. "Coq.Logic.Epsilon" *)

  val classical : t
  (** The prelude requiring classical Logic, i.e "Coq.Logic.Classical" *)

  val require : ?deps:S.t -> string -> t
  (** Add a "Require  mport" prelude *)

  val abbrev : ?deps:S.t -> 'a Expr.id ->
    (Format.formatter -> 'a Expr.id -> unit) -> t
  (** Add a notation for identifiers. *)

end

(** {2 Tactic helpers} *)

val tactic :
  ?prefix:string ->
  ?normalize:(Expr.formula selector) ->
  ?prelude:prelude list ->
  (Format.formatter -> Proof.Ctx.t -> unit) -> tactic
(** Create a tactic. *)

val exact : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Helper to use the 'exact' coq tactic. *)

val pose_proof : Proof.Ctx.t -> Expr.formula ->
  Format.formatter -> ('a, Format.formatter, unit) format -> 'a
(** Helper to use the 'pose proof' coq tactic. *)

val fun_binder : Format.formatter -> _ Expr.id list -> unit
(** Helper to print function arguments, effectively prints the
    space-separated list of ids. *)

val app_t : Proof.Ctx.t -> Format.formatter -> Expr.formula * Expr.term list -> unit
(** Helper to print the application of the named formula to a list of arguments. *)

val sequence : Proof.Ctx.t ->
  (string -> Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a list -> string
(** Print a sequence of inference.
    TODO: more explicit documentation. *)


(** {2 Printing expressions} *)

module Print : sig


  (** {2 Modifying printing} *)

  val pretty : Expr.Print.pretty Expr.tag
  (** Pretty tag to change the pinted name of a symbol, and/or
      control whether it is an infix or prefix symbol. *)

  val trap_ty : Expr.ty -> Expr.ty -> unit
  val trap_term : Expr.term -> Expr.term -> unit
  (** "Trap" types and terms. A trapped type or term will be replaced
      with its associated type/term when printing. *)


  (** {2 Effective Printing} *)

  val id : Format.formatter -> _ Expr.id -> unit
  val dolmen : Format.formatter -> Dolmen.Id.t -> unit

  val ty : Format.formatter -> Expr.ty -> unit
  val term : Format.formatter -> Expr.term -> unit
  val formula : Format.formatter -> Expr.formula -> unit

  val path : Format.formatter -> int * int -> unit
  val path_to : Format.formatter -> Expr.formula * Expr.f_order -> unit

  val pattern :
    start:(Format.formatter -> unit -> unit) ->
    stop:(Format.formatter -> unit -> unit) ->
    sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a Expr.order -> unit

  val pattern_or :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a Expr.order -> unit
  val pattern_and :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a Expr.order -> unit
  val pattern_ex :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a Expr.order -> unit
  val pattern_intro_and :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a Expr.order -> unit

end

