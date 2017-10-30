
val section : Section.t
(** Main section for proofs *)


(** {2 Pretty printing info} *)

module Pretty : sig
  (** Pretty printing information for symbols. Contains
      language-specific information related to printing,
      such as default associativity, infix notation, and
      name to use. *)

  type assoc =
    | Left  (** symbolis left associative *)
    | Right (** symbol is right associative *)
  (** Associativity of symbols *)

  type t = {
    infix   : bool;
    name    : string;
    assoc   : assoc option;
  }
  (** Pretty printing information (for a specific language). *)

  val mk : ?assoc:assoc -> ?infix:bool -> string -> t
  (** Create a pretty ptingin information record. *)

end


(** {2 Terms} *)

type binder = private
  | Pi      (** Dependant product *)
  | Arrow   (** Function type *)
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
  term : descr;
  mutable hash : int;
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


(** {2 Term inspection} *)

val hash : t -> int
(** standard hash function *)

val equal : t -> t -> bool
(** standard equality function *)

val compare: t -> t -> int
(** standard comparison function *)

val print : Format.formatter -> t -> unit
(** Print a term (quite verbose). *)


(** {2 Term creation} *)

val _Type : t
(** The term at the root of everything. *)

val _Prop : t
(** The term for the type of propositions. *)

val const : id -> t
(** reate a term from an identifier. *)

val app : t -> t -> t
val apply : t -> t list -> t
(** Term application (curried and uncurried). *)

val letin : id -> t -> t -> t
(** Local let, as [letin v e body],binds [v] to [e] in [body]. *)

val pi : id -> t -> t
val pis : id list -> t -> t
(** Dependant product. *)

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


(** {2 Term substitution} *)

module Subst : Map.S with type key = id
(** Substitutions, aka mapping from variables to terms. *)

val subst : t Subst.t -> t -> t
(** Substitution on terms. Correctly handles *)


(** {2 Term destruction} *)

val uncurry_app : t -> t * t list
(** Uncurry the application. *)

val uncurry : ?tag:(Pretty.t Tag.t) -> t ->
  [ `Infix of t * t list
  | `Prefix of t * t list ]
(** Uncurry a term, using the associtivity information
    in the tag. *)

val uncurry_assoc_left : id -> t list -> t list
val uncurry_assoc_right : id -> t list -> t list
(** Uncurry a left (or right) associative symbol in a term. *)


