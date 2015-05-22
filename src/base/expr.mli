
(** Expressions for TabSat *)

(** {2 Type definitions} *)
type multiplicity =
  | Linear
  | Infinite

type 't eval =
  | Interpreted of 't * int
  | Waiting of 't

(** {3 Variables} *)
type hash
type var_id = private int
type status = private int
type tag_map = private Tag.map

type 'a tag = 'a Tag.t
type 'a meta_index = private int

type 'ty var = private {
  var_name : string;
  var_id : var_id; (** unique *)
  var_type : 'ty;
}

type 'ty meta = private {
  meta_var : 'ty var;
  meta_mult : multiplicity;
  meta_index : 'ty meta_index;
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
  ty_tags : tag_map;
  ty_status : status;
  mutable ty_hash : hash; (** Use Ty.hash instead *)
}

(** {3 Terms} *)

type term_descr = private
  | Var of ty var
  | Meta of ty meta
  | App of ty function_descr var * ty list * term list

and term = private {
  term    : term_descr;
  t_type  : ty;
  t_tags : tag_map;
  t_status : status;
  mutable t_hash : hash; (** Use Term.hash instead *)
}

(** {3 Formulas} *)

type free_args = ty list * term list

type formula_descr = private
  (** Atoms *)
  | Pred of term
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
  | All of ty var list * free_args * formula
  | AllTy of ttype var list * free_args * formula
  | Ex of ty var list * free_args * formula
  | ExTy of ttype var list * free_args * formula

and formula = private {
  f_tags : tag_map;
  formula : formula_descr;
  mutable f_hash : hash; (** Use Formula.hash instead *)
  mutable f_vars : (ttype var list * ty var list) option;
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

module Debug : sig
  (** Verbose printing functions for debug pruposes *)

  val var : Buffer.t -> 'a var -> unit
  val var_ty : Buffer.t -> ty var -> unit
  val var_ttype : Buffer.t -> ttype var -> unit

  val const_ty : Buffer.t -> ty function_descr var -> unit
  val const_ttype : Buffer.t -> ttype function_descr var -> unit

  val meta : Buffer.t -> 'a meta -> unit

  val ty : Buffer.t -> ty -> unit
  val fun_ty : Buffer.t -> ty function_descr -> unit

  val ttype : Buffer.t -> ttype -> unit
  val fun_ttype : Buffer.t -> ttype function_descr -> unit

  val term : Buffer.t -> term -> unit
  val formula : Buffer.t -> formula -> unit
end

module Print : sig
  (** Pretty printing functions *)

  val var : Format.formatter -> 'a var -> unit
  val var_ty : Format.formatter -> ty var -> unit
  val var_ttype : Format.formatter -> ttype var -> unit

  val meta : Format.formatter -> 'a meta -> unit

  val ty : Format.formatter -> ty -> unit
  val ttype : Format.formatter -> ttype -> unit

  val term : Format.formatter -> term -> unit
  val formula : Format.formatter -> formula -> unit
end

(** {5 status} *)

module Status : sig
  val goal : status
  val hypothesis : status
  (** Standard status for goals (theorem/lemmas to prove), and hypothesis (assumptions) repectly.
      Unless otherwise specified, types and terms have hypothesis status. *)
end

(** {2 Variables & Metas} *)

module Var : sig
  type 'a t = 'a var
  (* Type alias *)

  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  (** Usual functions for hash/comparison *)

  val print : Format.formatter -> 'a t -> unit
  val debug : Buffer.t -> 'a t -> unit
  (** Printing for variables *)

  val prop : ttype function_descr var
  (** Constant representing the type for propositions *)

  val ttype : string -> ttype var
  (** Create a fresh type variable with the given name. *)

  val ty : string -> ty -> ty var
  (** Create a fresh variable with given name and type *)

  val ty_fun : string -> int -> ttype function_descr var
  (** Create a fresh type constructor with given name and arity *)

  val term_fun : string -> ttype var list -> ty list -> ty -> ty function_descr var
  (** [ty_fun name type_vars arg_types return_type] returns a new constant symbol,
      possibly polymorphic with respect to the variables in [type_vars] (which may appear in the
      types in [arg_types] and in [return_type]). *)

  val ty_skolem : ttype var -> ttype function_descr var
  val term_skolem : ty var -> ty function_descr var
  (** Returns the skolem symbols associated with the given variables. The skolems
      symbols take as arguments the free_variables of their defining formula.
      For simplicity, just apply the skolem to the free_args of the quantified expression. *)

  val occurs_term : ty var -> term -> bool
  (** Returns [true] if the given variable occurs in the term.
      WARNING: since meta-variables are wrapped variables, it can yield unexpected results. *)

  val set_eval : 'a var -> int -> (term -> term eval) -> unit
  val set_assign : 'a var -> int -> (term -> term) -> unit
  (** [set_eval v n f] sets f as the handler to call in order to
      eval or assign the given variable, with priority [n] (only the handler with
      highest priority is called. *)

  val is_interpreted : 'a var -> bool
  val is_assignable : 'a var -> bool
  (** Returns [true] if a handler has been set up for the given variable. *)

end

module Meta : sig
  type 'a t = 'a meta
  (** Type alias *)

  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  (** Usual functions for hash/comparison *)

  val print : Format.formatter -> 'a t -> unit
  val debug : Buffer.t -> 'a t -> unit
  (** Printing for metavariables *)

  val of_all_ty : formula -> ttype meta list
  (** Given a formula [f] which is either a universal quantification over types,
      or the negation of an existencial quantification over types,
      returns a list of meta-variables associated with [f]. *)

  val of_all : formula -> ty meta list
  (** Given a formula [f] which is either a universal quantification over terms,
      or the negation of an existencial quantification over terms,
      returns a list of meta-variables associated with [f]. *)

  val ty_def : ty meta_index -> formula
  val ttype_def : ttype meta_index -> formula
  (** Returns the formula associated with a given meta index. *)

  val of_ty_index : ty meta_index -> ty meta list
  val of_ttype_index : ttype meta_index -> ttype meta list
  (** Returns the list of all metas sharing the given index. *)

  val in_ty : ty -> ttype meta list * ty meta list
  val in_term : term -> ttype meta list * ty meta list
  (** Returns the list of meta-variable occuring in the argument *)

end

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

  val debug :
    (Buffer.t -> 'a -> unit) ->
    (Buffer.t -> 'b -> unit) ->
    Buffer.t -> ('a, 'b) t -> unit
  (** Prints the substitution, using the given functions to print keys and values. *)

  val print :
    (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) ->
    Format.formatter -> ('a, 'b) t -> unit
  (** Prints the substitution, using the given functions to print keys and values. *)

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

(** {2 Types} *)

module Ty : sig
  type t = ty
  (** Type alias *)

  type subst = (ttype var, ty) Subst.t
  (** The type of substitutions over types. *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual hash/compare functions *)

  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
  val debug_subst : Buffer.t -> subst -> unit
  (** Printing functions *)

  val prop : ty
  (** The type of propositions *)

  val of_var : ?status:status -> ttype var -> ty
  (** Creates a type from a variable *)

  val of_meta : ?status:status -> ttype meta -> ty
  (** Create a type from a meta-variable *)

  val apply : ?status:status -> ttype function_descr var -> ty list -> ty
  (** Applies a constant to a list of types *)

  val subst : subst -> ty -> ty
  (** Substitution over types. *)

  val fv : ty -> ttype var list * ty var list
  (** Return the list of free variables in the given type.
      Here, the [ty var list] is guaranteed to be empty. *)

  val tag : ty -> 'a tag -> 'a -> ty
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : ty -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

module Term : sig
  type t = term
  (** Type alias *)

  type subst = (ty var, term) Subst.t
  (** The type of substitutions in types. *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (**  Usual hash/compare functions *)

  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
  val debug_subst : Buffer.t -> subst -> unit
  (** Printing functions *)

  val of_var : ?status:status -> ty var -> term
  (** Create a term from a variable *)

  val of_meta : ?status:status -> ty meta -> term
  (** Create a term from a meta-variable *)

  val apply : ?status:status -> ty function_descr var -> ty list -> term list -> term
  (** Applies a constant function to type arguments, then term arguments *)

  val subst : Ty.subst -> subst -> term -> term
  (** Substitution over types. *)

  val replace : term * term -> term -> term
  (** [replace (t, t') t''] returns the term [t''] where every occurence of [t]
      has been replace by [t']. *)

  val fv : term -> ttype var list * ty var list
  (** Return the list of free variables in the given term. *)

  val eval : term -> term eval
  val assign : term -> term
  (** Evaluate or assigns the given term using the handler of the
      head symbol of the expression, see the Var module. *)

  val tag : term -> 'a tag -> 'a -> term
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : term -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

module Formula : sig
  type t = formula
  (** Type alias *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual hash/compare functions *)

  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
  (** Printing functions *)

  val f_true : formula
  val f_false : formula
  (** Formula for the true and false constants *)

  val eq : term -> term -> formula
  (** Create an equality over two terms. The two given terms
      must have the same type [t], which must be different from {!Ty.prop} *)

  val pred : term -> formula
  (** Create a formula from a term. The given term must have type {!Ty.prop} *)

  val neg : formula -> formula
  (** Returns the negation of the given formula *)

  val f_and : formula list -> formula
  (** Returns the conjunction of the given formulas *)

  val f_or : formula list -> formula
  (** Returns the disjunction of the given formulas *)

  val imply : formula -> formula -> formula
  (** [imply p q] returns a formula representing [p] implies [q]. *)

  val equiv : formula -> formula -> formula
  (** [equi p q] returns a formula representing [p] equivalent to [q] *)

  val all : ty var list -> formula -> formula
  val allty : ttype var list -> formula -> formula
  (** Universally quantify the given formula over the given variables *)

  val ex : ty var list -> formula -> formula
  val exty : ttype var list -> formula -> formula
  (** Existentially quantify the given formula over the given variables *)

  val subst : Ty.subst -> Term.subst -> formula -> formula
  (** Substitution over formulas *)

  val partial_inst : Ty.subst -> Term.subst -> formula -> formula
  (** Make a partial instanciation of the given formula with the substitutions. *)

  val fv : formula -> ttype var list * ty var list
  (** Return the list of free variables in the given formula. *)

  val tag : formula -> 'a tag -> 'a -> formula
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : formula -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

