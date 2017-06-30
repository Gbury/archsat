
(** Expressions for TabSat *)

(** {2 Type definitions} *)

(** These are custom types used in functions later. *)

(** {3 Identifiers} *)

(** Identifiers are the basic building blocks used to build types terms and expressions
    in tabsat. *)

type hash
type index = private int
type status = private int
type tag_map = private Tag.map
type 'a meta_index = private int

(** Private aliases to provide access. You should not have any need
    to use these, instead use the functions provided by this module. *)

type 'a tag = 'a Tag.t

(** Alias to shorten type definition. *)

type builtin = ..
type builtin += Base

(** Builtin tags, used to assign semantic meaning to symbols. *)

type 'ty id = private {
  id_type : 'ty;
  id_name : string;
  index   : index; (** unique *)
  builtin : builtin;
}

(** The type of identifiers. An ['a id] is an identifier whose solver-type
    is represented by an inhabitant of type ['a].
    All identifier have an unique [index] which is used for comparison,
    so that the name of a variable is only there for tracability
    and/or pretty-printing. *)

type 'ty meta = private {
  meta_id : 'ty id;
  meta_index : 'ty meta_index;
}

(** A meta-variable is a wrapped variable. They are used as "free variables"
    as is sometimes said in tableau-related litterature. Intuitively they are
    variables that can be unified with terms or types. *)

(** {3 Types} *)

type ttype = Type

(** The caml type of solver-types. *)

type 'ty function_descr = private {
  fun_vars : ttype id list; (** prenex forall *)
  fun_args : 'ty list;
  fun_ret : 'ty;
}

(** This represents the solver-type of a function.
    Functions can be polymorphic in the variables described in the
    [fun_vars] field. *)

type ty_descr = private
  | TyVar of ttype id
  (** bound variables (i.e should only appear under a quantifier) *)
  | TyMeta of ttype meta
  (** meta-variables *)
  | TyApp of ttype function_descr id * ty list
  (** application of a constant to some arguments *)

and ty = private {
  ty : ty_descr;
  ty_status : status;
  mutable ty_tags : tag_map;
  mutable ty_hash : hash; (** Use Ty.hash instead *)
}

(** These types defines solver-types, i.e the representation of the types
    of terms in the solver. Record definition for [type ty] is shown in order
    to be able to use the [ty.ty] field in patter matches. Other fields shoud not
    be accessed directly, but throught the functions provided by the [Ty] module. *)

(** {3 Terms} *)

type term_descr = private
  | Var of ty id
  (** bound variables (i.e should only appear under a quantifier) *)
  | Meta of ty meta
  (** meta-variables *)
  | App of ty function_descr id * ty list * term list
  (** application of a constant to some arguments *)

and term = private {
  term     : term_descr;
  t_type   : ty;
  t_status : status;
  mutable t_tags : tag_map;
  mutable t_hash : hash; (** Do not use this filed, call Term.hash instead *)
}

(** Types defining terms in the solver. The definition is vary similar to that
    of solver-types, except for type arguments of polymorphic functions which
    are explicit. This has the advantage that there is a clear and typed distinction
    between solver-types and terms, but may lead to some duplication of code
    in some places. *)

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
  | All of ty id list * free_args * formula
  | AllTy of ttype id list * free_args * formula
  | Ex of ty id list * free_args * formula
  | ExTy of ttype id list * free_args * formula

and formula = private {
  formula : formula_descr;
  mutable f_tags : tag_map;
  mutable f_hash : hash; (** Use Formula.hash instead *)
  mutable f_vars : (ttype id list * ty id list) option;
}
(** The type of formulas in the solver. The list of free arguments in quantifiers
    is a bit tricky, so you should not touch it
    (TODO: further explanations in full doc?). *)

type t_order =
  | Same
  | Inverse

val t_order : t_order Tag.t
(** Tags containing information about the order of arguments for equalities. *)

type f_order =
  | F of formula
  | L of f_order list

val f_order : f_order Tag.t
(** Tags containing information about the inital order of arfuments for the
    [And] and [Or] constructions. *)

(** {3 Exceptions} *)

exception Type_mismatch of term * ty * ty
(* Raised when as Type_mismatch(term, actual_type, expected_type) *)

exception Bad_arity of ty function_descr id * ty list * term list
exception Bad_ty_arity of ttype function_descr id * ty list
(** Raised when trying to build an application with wrong arity *)

exception Cannot_assign of term
exception Cannot_interpret of term
(** Raised when requesting an assigner/interpreter for a variable, but none has been set. *)

(** {2 Printing} *)

module Print : sig
  (** Pretty printing functions *)

  val id : Format.formatter -> 'a id -> unit
  val id_ty : Format.formatter -> ty id -> unit
  val id_ttype : Format.formatter -> ttype id -> unit

  val const_ty : Format.formatter -> ty function_descr id -> unit
  val const_ttype : Format.formatter -> ttype function_descr id -> unit

  val meta : Format.formatter -> 'a meta -> unit

  val ty : Format.formatter -> ty -> unit
  val fun_ty : Format.formatter -> ty function_descr -> unit

  val ttype : Format.formatter -> ttype -> unit
  val fun_ttype : Format.formatter -> ttype function_descr -> unit

  val term : Format.formatter -> term -> unit
  val formula : Format.formatter -> formula -> unit
end

(** {2 Status} *)

module Status : sig
  val goal : status
  val hypothesis : status
  (** Standard status for goals (theorem/lemmas to prove), and hypothesis (assumptions) repectly.
      Unless otherwise specified, types and terms have hypothesis status. *)
end

(** {2 Identifiers & Metas} *)

module Id : sig

  include Sig.PolyFull with type 'a t = 'a id
  (** Base signature for parametric types. *)

  module Ty : Sig.Full with type t = ty id
  module Ttype : Sig.Full with type t = ttype id
  module Const : Sig.Full with type t = ty function_descr id
  module TyCstr : Sig.Full with type t = ttype function_descr id
  (** Concrete instances for functor application. *)

  val prop : ttype function_descr id
  val base : ttype function_descr id
  (** Constants representing the type for propositions and a default type
      for term, respectively. *)

  val ttype : ?builtin:builtin -> string -> ttype id
  (** Create a fresh type variable with the given name. *)

  val ty : ?builtin:builtin -> string -> ty -> ty id
  (** Create a fresh variable with given name and type *)

  val ty_fun : ?builtin:builtin -> string -> int -> ttype function_descr id
  (** Create a fresh type constructor with given name and arity *)

  val term_fun : ?builtin:builtin -> string -> ttype id list -> ty list -> ty -> ty function_descr id
  (** [term_fun name type_vars arg_types return_type] returns a fresh constant symbol,
      possibly polymorphic with respect to the variables in [type_vars] (which may appear in the
      types in [arg_types] and in [return_type]). *)

  val ty_skolem : ttype id -> ttype function_descr id
  val term_skolem : ty id -> ty function_descr id
  (** Returns the skolem symbols associated with the given variables. The skolems
      symbols take as arguments the free_variables of their defining formula.
      For simplicity, just apply the skolem to the free_args of the quantified expression. *)

  val occurs_in_term : ty id -> term -> bool
  (** Returns [true] if the given variable occurs in the term. *)

  val set_eval : 'a id -> int -> (term -> unit) -> unit
  (** [set_eval v n f] sets f as the handler to call in order to
      eval terms starting with the given variable, with priority [n]
      (only the handler with highest priority is calledi). *)

  val set_assign : 'a id -> int -> (term -> term) -> unit
  (** [set_assign v n f] sets f as the handler to call in order to
      assign terms starting with the given variable, with priority [n]
      (only the handler with highest priority is calledi). *)

  val is_assignable : 'a id -> bool
  val is_interpreted : 'a id -> bool
  (** Returns [true] if a handler has been set up for the given variable. *)

  val merge_fv :
    ttype id list * ty id list ->
    ttype id list * ty id list ->
    ttype id list * ty id list
  (** Merge lists of free variables *)

end

module Meta : sig

  include Sig.PolyFull with type 'a t = 'a meta
  (** Base interface *)

  module Ty : Sig.Full with type t = ty meta
  module Ttype : Sig.Full with type t = ttype meta
  (** Convenience modules *)

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

  val occurs_in_term : ty meta -> term -> bool
  (** Returns [true] if the given meta-variable occurs in the term. *)

  val merge_fm :
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list
  (** Merge lists of free meta-variables *)

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

  val map : ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
  (** Maps the given function over bound values *)

  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  (** Fold over the elements *)

  val merge :
    ('a -> 'b option -> 'c option -> 'd option) ->
    ('a, 'b) t -> ('a, 'c) t -> ('a, 'd) t
  (** Merge two substitutions *)

  val filter : ('a -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t
  (** Filter bindings base on a predicate. *)

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
    val bind : ('a key, 'b) t -> 'a key -> 'b -> ('a key, 'b) t
    (** [bind v t subst] returns the same substitution as [subst] with the additional binding from [v] to [t].
        Erases the previous binding of [v] if it exists. *)
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
    (** [remove v subst] returns the same substitution as [subst] except for [v] which is unbound in the returned substitution. *)
  end

  module Id : S with type 'a key = 'a id
  module Meta : S with type 'a key = 'a meta
end

(** {2 Types} *)

module Ty : sig

  include Sig.Full with type t = ty

  type var_subst = (ttype id, ty) Subst.t
  type meta_subst = (ttype meta, ty) Subst.t
  (** The type of substitutions over types. *)

  val prop : ty
  val base : ty
  (** The type of propositions and individuals *)

  val of_id : ?status:status -> ttype id -> ty
  (** Creates a type from a variable *)

  val of_meta : ?status:status -> ttype meta -> ty
  (** Create a type from a meta-variable *)

  val apply : ?status:status -> ttype function_descr id -> ty list -> ty
  (** Applies a constant to a list of types *)

  val subst : ?fix:bool -> var_subst -> meta_subst -> ty -> ty
  (** Substitution over types.
      @param fix wether to fixpoint the application of the substitution. *)

  val fv : ty -> ttype id list * ty id list
  val fm : ty -> ttype meta list * ty meta list
  (** Return the list of free variables (resp. meta-variables) in the given type.
      Here, the [ty id list] (resp. [ty meta list]) is guaranteed to be empty. *)

  val tag : ty -> 'a tag -> 'a -> unit
  (** Insert a local tag in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : ty -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

(** {2 Terms} *)

module Term : sig

  include Sig.Full with type t = term

  type var_subst = (ty id, term) Subst.t
  type meta_subst = (ty meta, term) Subst.t
  (** The type of substitutions in types. *)

  val of_id : ?status:status -> ty id -> term
  (** Create a term from a variable *)

  val of_meta : ?status:status -> ty meta -> term
  (** Create a term from a meta-variable *)

  val apply : ?status:status -> ty function_descr id -> ty list -> term list -> term
  (** Applies a constant function to type arguments, then term arguments *)

  val subst :
    ?fix:bool ->
    Ty.var_subst -> Ty.meta_subst ->
    var_subst -> meta_subst -> term -> term
  (** Substitution over terms.
      @param fix wether to fixpoint the substitution application *)

  val replace : term * term -> term -> term
  (** [replace (t, t') t''] returns the term [t''] where every occurence of [t]
      has been replaced by [t']. *)

  val fv : term -> ttype id list * ty id list
  val fm : term -> ttype meta list * ty meta list
  (** Return the list of free variables in the given term. *)

  val eval : ?strict:bool -> term -> unit
  (** Try and call the evaluation function associated with the term's
      head symbol. Returns [true] if the function has been succesfully
      found and called, and [false] else.
      @param strict if set, raise an exception when no handler is found (default: [false])
      @raise (Cannot_intepret t) if there is no evaluation handler,
        and [strict] is [true]
  *)

  val assign : term -> term
  (** Return a valid assignment for the given term using the handler of the
      head symbol of the expression, see the Var module.
      @raise (Cannot_assign t) if there is no assign handler
  *)

  val tag : term -> 'a tag -> 'a -> unit
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : term -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

(** {2 Formulas} *)

module Formula : sig

  include Sig.Full with type t = formula

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

  val all : ty id list -> formula -> formula
  val allty : ttype id list -> formula -> formula
  (** Universally quantify the given formula over the given variables *)

  val ex : ty id list -> formula -> formula
  val exty : ttype id list -> formula -> formula
  (** Existentially quantify the given formula over the given variables *)

  val subst :
    ?fix:bool ->
    Ty.var_subst -> Ty.meta_subst ->
    Term.var_subst -> Term.meta_subst ->
    formula -> formula
  (** Substitution over formulas
      @param fix wther to fixpoint the substitution application *)

  val partial_inst : Ty.var_subst -> Term.var_subst -> formula -> formula
  (** Make a partial instanciation of the given formula with the substitutions. *)

  val fv : formula -> ttype id list * ty id list
  (** Return the list of free variables in the given formula. *)

  val tag : formula -> 'a tag -> 'a -> unit
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : formula -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

