(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

val section : Section.t
(** Main section for proofs *)

module S = Expr.Subst
(** Alias module for substitutions *)

(** {2 Terms} *)

type binder =
  | Lambda  (** Function binder *)
  | Forall  (** Universal quantification *)
  | Exists  (** Existencial quantification *)
(** Available binders *)

type id = t Expr.id

and descr = private
  | Type
  (** The Universe at the root of everything *)
  | Id of id
  (** Identifiers (i.e variables, constants) *)
  | App of t * t
  (** Curried appliation *)
  | Let of id * t * t
  (** Local let binding, as (var, expr, body). *)
  | Binder of binder * id * t
  (** Variable binding, without argument/value *)
(** Term descriptors. *)

and t = private {
  ty : t;
  hash : int;
  index : int;
  term : descr;
  reduced : t Lazy.t;
  free : (id, int) S.t;
}
(** Term records. Contains the type of the term,
    to avoid recomputing it every time (which is pretty
    often in the context of proof checking). *)

exception Function_expected of t
(** Exception raised when applying a non-function to an argument.
    The given term is the one that's expected to be a function. *)

exception Type_mismatch of t * t
(** Exception raised during typechecking of application, with a
    pair [(arg, ty)] where [arg] is the provided argument and
    [ty] the expected type of the argument. *)

exception Match_Impossible of t * t
(** Raised during pattern matching when incompatible terms
    are being matched. *)


(** {2 Term inspection} *)

(** {4 Standard functions} *)

val hash : t -> int
(** standard hash function *)

val equal : t -> t -> bool
(** standard equality function *)

val compare: t -> t -> int
(** standard comparison function *)

val print : Format.formatter -> t -> unit
val print_typed : Format.formatter -> t -> unit
(** Print a term (quite verbose). *)

module Reduced : sig
  type nonrec t = t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end
(** Standard function that take the reduced (or normal form) into account
    rather than the base term. *)

(** {4 Meta data accessor} *)

val ty : t -> t
(** Returns the type of a term. *)

val reduce : t -> t
(** Compute the beta-normal form of the term. *)

val is_reduced : t -> bool
(** Is the given term in normal form ?
    WARNING: the type of a term in normal form is not necessary in normal form. *)

val beta_simplify : t -> t
(** Simplify a term (hopefully faster than reduce) *)

(** {4 Disambiguation}
    Variables can share the same name because theyr are not identified by name
    but rather by unique ids. Thus when pretty printing terms, there may be
    name collisions. The {!disambiguate} function tags variables using the
    {!disambiguate_tag} so that there is no collision on the tagged names.
*)

val disambiguate_tag : Pretty.name Tag.t
(** Disambiguation tag. *)

val disambiguate : t -> unit
(** Disambiguate variables to avoid name capture. *)


(** {4 Variables} *)

val is_var : id -> bool
(** Is the given identifier a variable ? or a constant ?. *)

val free_vars : t -> (id, int) S.t
(** Computes the set of free variable sin a term. *)

val occurs : id -> t -> bool
(** Does the variable occurs in the set of free variables of
    the given term. *)


(** {4 Printing flags} *)

val dot_implicit : id -> unit
val is_dot_implicit : id -> bool
(** Mark.recognize coq implicit arguments. *)

val coq_implicit : id -> unit
val is_coq_implicit : id -> bool
(** Mark.recognize coq implicit arguments. *)

val coq_inferred : id -> unit
val is_coq_inferred : id -> bool
(** Mark.recognize coq arguments that can be inferred by coq,
    and thus can be printed using "_". *)

val tptp_implicit : id -> unit
val is_tptp_implicit : id -> bool
(** Mark.recognize coq implicit arguments. *)


(** {2 Id creation} *)

val var : string -> t -> id
(** [var name ty] creates a new variable of type [ty]. *)

val declare : string -> t -> id
(** [delcare name ty] declare a new symbol of type [ty]. *)

val define : string -> t -> id
(** [define name t] defines a new symbol, equal to [t], and with the same type. *)


(** {2 Term creation} *)

val _Type : t
(** The term at the root of everything. *)

val _Prop : t
val _Prop_id : id
(** The term for the type of propositions. *)

val id : id -> t
(** reate a term from an identifier. *)

val app : t -> t -> t
val apply : t -> t list -> t
(** Term application (curried and uncurried). *)

val letin : id -> t -> t -> t
(** Local let, as [letin v e body],binds [v] to [e] in [body]. *)

val bind : binder -> id -> t -> t
(** Generic binder application. *)

val lambda : id -> t -> t
val lambdas : id list -> t -> t
(** Function construction. *)

val arrow : t -> t -> t
val arrows : t list -> t -> t
(** Function type creation. *)

val forall : id -> t -> t
val foralls : id list -> t -> t
(** Universal quantification. *)

val exist : id -> t -> t
val exists : id list -> t -> t
(** Existencial quantification. *)


(** {2 Term constants} *)

val true_id : id
val true_term : t
(** [true] constant *)

val false_id : id
val false_term : t
(** [false] constant *)

val equal_id : id
val equal_term : t
(** equality *)

val not_id : id
val not_term : t
(** Propositional negation *)

val imply_id : id
val imply_term : t
(** Propostional implication *)

val equiv_id : id
val equiv_term : t
(** Propositional equivalence *)

val or_id : id
val or_term : t
(** Propositional disjunction *)

val and_id : id
val and_term : t
(** Propositional conjunction *)


(** {2 Term translation} *)

type callback = id -> unit
type 'a translator = ?callback:callback -> 'a -> t
(** Type for callbacks and translators.
    Callbacks are called on every identifier inferred during translation. *)

val of_unit : unit translator
val of_ttype : Expr.ttype translator
val of_ty : Expr.ty translator
val of_term : Expr.term translator
val of_formula : Expr.formula translator
(** Translating expressions into terms. *)

val of_id :
  kind:[`Var | `Declared | `Cst] -> 'a translator -> 'a Expr.id translator
val of_id_aux :
  kind:[`Var | `Declared | `Cst] -> 'a translator -> ?callback:callback -> 'a Expr.id -> id
val of_function_descr :
  'a translator -> 'b translator -> ('a, 'b) Expr.function_descr translator
(** Translating functions *)

val trap_id : _ Expr.id -> id -> unit
val trap_ty : Expr.ty -> t -> unit
val trap_term : Expr.term -> t -> unit
(** Force translation for given types and terms. *)

val trap : (unit -> unit) -> unit
(** Allow to register a "trap", basically a side-effect computation,
    in relation to translation to proof terms. Since translation of complex
    proof terms can be costly (most notably epsilon terms), it is advisable
    to delay them until "after" proof search, and perform it only if proof ouptut
    is activated. *)

val clean_traps : unit -> unit
(** Call all registered traps. *)


(** {2 Term substitution} *)

val subst : (id, t) S.t -> t -> t
(** Substitution on terms. Correctly handles *)

val pmatch : pat:t -> t -> (id, t) S.t
(** Pattern matching on terms.
    @raise Match_Impossible if pattern matching is not possible. *)


(** {2 Term destruction} *)

val contract : t -> t
(** Try and contract the term to return a smaller equivalent term
    (useful when printing). *)

val uncurry_app : t -> t * t list
(** Uncurry the application. *)

val uncurry : ?assoc:Pretty.assoc Expr.tag -> t -> t * t list
(** Uncurry a term, using the associtivity information
    in the tag. *)

val uncurry_assoc_left : id -> t list -> t list
val uncurry_assoc_right : id -> t list -> t list
(** Uncurry a left (or right) associative symbol in a term. *)

val flatten_binder : t -> [ `Pi | `Arrow | `Binder of binder ] * id list * t
(** [flatten_binder t] returns the list of all consecutive variables bound by the
    same binder, correctly identifying arrow terms (i.e foralls where the variable
    does not occur in the body). *)

val concat_vars : id list -> (t * id list) list
(** Groups variables by types. *)


