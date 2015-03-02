
(** Expressions for TabSat *)

(** {2 Type definitions} *)

(** {3 Variables} *)
type var_id = private int
type meta_index = private int

type 'ty var = private {
  var_name : string;
  var_id : var_id; (** unique *)
  var_type : 'ty;
}

type 'ty meta = private {
  meta_var : 'ty var;
  meta_index : meta_index;
  can_unify : bool;
}

(** {3 Types} *)

type ttype = Type
(** The type of types in the AST *)

and 'ty function_descr = private {
  fun_vars : ttype var list; (** prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

type ty_descr = private
  | TyVar of ttype var
  | TyMeta of ttype meta
  | TyApp of ttype function_descr var * ty list

and ty = private {
  ty : ty_descr;
  mutable ty_hash : int; (** Use Ty.hash instead *)
}

(** {3 Terms} *)

type term_descr = private
  | Var of ty var
  | Meta of ty meta
  | App of ty function_descr var * ty list * term list

and term = private {
  term    : term_descr;
  t_type  : ty;
  mutable t_hash : int; (** Use Term.hash instead *)
}

(** {3 Formulas} *)

type free_vars = ty list * term list

type formula_descr = private
  | Pred of term (** Atoms *)
  | Equal of term * term

  (** Prop constructors *)
  | True
  | False
  | Not of formula
  | And of formula list
  | Or of formula list
  | Imply of formula * formula
  | Equiv of formula * formula

  (** Quantifiers *)
  | All of ty var list * free_vars * formula
  | AllTy of ttype var list * free_vars * formula
  | Ex of ty var list * free_vars * formula
  | ExTy of ttype var list * free_vars * formula

and formula = private {
  formula : formula_descr;
  mutable f_hash : int; (** Use Formula.hash instead *)
}

(** {3 Exceptions} *)

exception Type_error_doublon of string * int
exception Type_error_app of ty function_descr var * ty list * term list
exception Type_error_ty_app of ttype function_descr var * ty list
exception Type_error_mismatch of ty * ty

exception Cannot_assign of term
exception Cannot_interpret of term

exception Subst_error_ty_scope of ttype var
exception Subst_error_term_scope of ty var

(** {2 Printing} *)

val debug_var : Buffer.t -> 'a var -> unit
val debug_var_ty : Buffer.t -> ty var -> unit
val debug_var_ttype : Buffer.t -> ttype var -> unit

val debug_const_ty : Buffer.t -> ty function_descr var -> unit
val debug_const_ttype : Buffer.t -> ttype function_descr var -> unit

val debug_meta : Buffer.t -> 'a meta -> unit

val debug_ty : Buffer.t -> ty -> unit
val debug_fun_ty : Buffer.t -> ty function_descr -> unit
val debug_ttype : Buffer.t -> ttype -> unit
val debug_fun_ttype : Buffer.t -> ttype function_descr -> unit

val debug_term : Buffer.t -> term -> unit
val debug_formula : Buffer.t -> formula -> unit
(** Verbose printing functions for debug pruposes *)

val print_var : Format.formatter -> 'a var -> unit
val print_var_ty : Format.formatter -> ty var -> unit
val print_var_ttype : Format.formatter -> ttype var -> unit

val print_meta : Format.formatter -> 'a meta -> unit

val print_ty : Format.formatter -> ty -> unit
val print_ttype : Format.formatter -> ttype -> unit

val print_term : Format.formatter -> term -> unit
val print_formula : Format.formatter -> formula -> unit
(** Pretty printing functions *)


(** {2 Hashs & Comparisons} *)

module Var : sig
  type 'a t = 'a var
  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  val print : Format.formatter -> 'a t -> unit
  val debug : Buffer.t -> 'a t -> unit
end
module Meta : sig
  type 'a t = 'a meta
  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  val print : Format.formatter -> 'a t -> unit
  val debug : Buffer.t -> 'a t -> unit
end
module Ty : sig
  type t = ty
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
end
module Term : sig
  type t = term
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
end
module Formula : sig
  type t = formula
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
end

(** {2 Constructors} *)

(** {5 Variables & Constants} *)

val ttype_var : string -> ttype var
val ty_var : string -> ty -> ty var

val type_const : string -> int -> ttype function_descr var
val term_const : string -> ttype var list -> ty list -> ty -> ty function_descr var

(** {5 Metas} *)

val get_meta_def : meta_index -> formula
val get_meta_ty_def : meta_index -> formula

val new_ty_metas : formula -> ttype meta list
val ty_metas_of_index : meta_index -> ttype meta list

val new_term_metas : formula -> ty meta list
val term_metas_of_index : meta_index -> ty meta list
(** [other_term_metas m] returns the list [l] of term metas that was generated together with [m]
    i.e [m] is a meta in [l] and [l] was returned by [new_term_metas] previously. *)

val protect : 'a meta -> 'a meta
(** Returns a meta equal to its argument, but that shouldn't be unified. (field 'can_unify' set to false) *)

(** {5 Skolems symbols} *)

val get_ty_skolem : ttype var -> ttype function_descr var
val get_term_skolem : ty var -> ty function_descr var
(** Returns the skolem symbols associated with the given functions. Should be
    applied to the [free_vars] arguments of the quantifier binding. *)

(** {5 Types} *)

val type_prop : ty
val prop_cstr : ttype function_descr var

val type_var : ttype var -> ty
val type_meta : ttype meta -> ty
val type_app : ttype function_descr var -> ty list -> ty

(** {5 Terms} *)

val term_var : ty var -> term
val term_meta : ty meta -> term
val term_app : ty function_descr var -> ty list -> term list -> term

(** {5 Formulas} *)

val f_true : formula
val f_false : formula

val f_equal : term -> term -> formula
val f_pred : term -> formula
val f_not : formula -> formula
val f_and : formula list -> formula
val f_or : formula list -> formula
val f_imply : formula -> formula -> formula
val f_equiv : formula -> formula -> formula
val f_all : ty var list -> formula -> formula
val f_allty : ttype var list -> formula -> formula
val f_ex : ty var list -> formula -> formula
val f_exty : ttype var list -> formula -> formula

(** { 2 Interpretation and Assignations} *)

type 't eval =
  | Interpreted of 't * int
  | Waiting of 't

val set_eval : 'a var -> int -> (term -> term eval) -> unit
val set_assign : 'a var -> int -> (term -> term) -> unit
(** [set_eval v n f] sets f as the handler to call in order to
    eval or assign the given variable, with priority [n] (only the handler with
    highest priority is called. *)

val is_interpreted : 'a var -> bool
val is_assignable : 'a var -> bool
(** Returns [true] if a handler has been set up for the given variable. *)

val eval : term -> term eval
val assign : term -> term
(** Evaluate or assigns the given term using the handler of the
    head symbol of the expression. *)

(** {2 Inspection} *)

val var_occurs : ty var -> term -> bool
(** Returns wether the given variable occurs in the term (including inside metas aud taus). *)

val ty_fv : ty -> ttype var list * ty var list
val term_fv : term -> ttype var list * ty var list
val formula_fv : formula -> ttype var list * ty var list
(** Returns the free variables of a given expression, that is the variables that
    are not bound by a quantifier. *)

(** {2 Substitutions} *)

module Subst : sig
  (** Module to handle substitutions *)

  type ('a, 'b) t
  (** The type of substitutions from values of type ['a] to values of type ['b]. *)

  val empty : ('a, 'b) t
  (** The empty substitution *)

  val is_empty : ('a, 'b) t -> bool
  (** Test wether a substitution is empty *)

  val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
  (** Iterates over the bindings of the substitution. *)

  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  (** Fold over the elements *)

  val bindings : ('a, 'b) t -> ('a * 'b) list
  (** Returns the list of bindings ofa substitution. *)

  val exists : ('a -> 'b -> bool) -> ('a, 'b) t -> bool
  (** Tests wether the predicate holds for at least one binding. *)

  val for_all : ('a -> 'b -> bool) -> ('a, 'b) t -> bool
  (** Tests wether the predicate holds for all bindings. *)

  val hash : ('b -> int) -> ('a, 'b) t -> int
  val compare : ('b -> 'b -> int) -> ('a, 'b) t -> ('a, 'b) t -> int
  val equal : ('b -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t -> bool
  (** Comparison and hash functions, with a comparison/hash function on values as parameter *)

  val choose : ('a, 'b) t -> 'a * 'b
  (** Return one binding of the given substitution, or raise Not_found if the substitution is empty.*)

  (** {5 Concrete subtitutions } *)
  module type S = sig
    type 'a key
    val get : 'a key -> ('a key, 'b) t -> 'b
    (** [get v subst] returns the value associated with [v] in [subst], if it exists.
        @raise Not_found if there is no binding for [v]. *)
    val mem : 'a key -> ('a key, 'b) t -> bool
    (** [get v subst] returns wether there is a value associated with [v] in [subst]. *)
    val bind : 'a key -> 'b -> ('a key, 'b) t -> ('a key, 'b) t
    (** [bind v t subst] returns the same substitution as [subst] with the additional binding from [v] to [t].
        Erases the previous binding of [v] if it exists. *)
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
    (** [remove v subst] returns the same substitution as [subst] except for [v] which is unbound in the returned substitution. *)
  end

  module Var : S with type 'a key = 'a var
  module Meta : S with type 'a key = 'a meta
end

type ty_subst = (ttype var, ty) Subst.t
type term_subst = (ty var, term) Subst.t
(** Abreviations for the substitution of types and terms respectively. *)

val type_subst : ty_subst -> ty -> ty
val term_subst : ty_subst -> term_subst -> term -> term
val formula_subst : ty_subst -> term_subst -> formula -> formula
(** Substitution functions for types, terms and formulas. *)

