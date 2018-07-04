
(** Expressions for TabSat *)

(** {2 Type definitions} *)

(** These are custom types used in functions later. *)

(** {3 Identifiers} *)

(** Identifiers are the basic building blocks used to build types terms and expressions
    in archsat. *)

type hash
type status
type index = private int
type tag_map = Tag.map
type meta_index = private int

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
  mutable id_tags : tag_map;
}

(** The type of identifiers. An ['a id] is an identifier whose solver-type
    is represented by an inhabitant of type ['a].
    All identifier have an unique [index] which is used for comparison,
    so that the name of a variable is only there for tracability
    and/or pretty-printing. *)

type 'ty meta = private {
  meta_id : 'ty id;
  meta_type : 'ty;
  meta_index : meta_index;
}

(** A meta-variable is a wrapped variable. They are used as "free variables"
    as is sometimes said in tableau-related litterature. Intuitively they are
    variables that can be unified with terms or types. *)

(** {3 Types} *)

type ttype = Type

(** The caml type of solver-types. *)

type ('ttype, 'ty) function_descr = private {
  fun_vars : 'ttype id list; (** prenex forall *)
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
  | TyApp of (unit, ttype) function_descr id * ty list
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
  | App of (ttype, ty) function_descr id * ty list * term list
  (** application of a constant to some arguments *)

and term = private {
  term     : term_descr;
  t_type   : ty;
  t_status : status;
  mutable t_tags : tag_map;
  mutable t_hash : hash; (** Do not use this field, call Term.hash instead *)
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
  | Ex of (ttype id list * ty id list) * free_args * formula
  | All of (ttype id list * ty id list) * free_args * formula

and formula = private {
  formula : formula_descr;
  f_status : status;
  mutable f_tags : tag_map;
  mutable f_hash : hash; (** Use Formula.hash instead *)
  mutable f_vars : (ttype id list * ty id list) option;
}
(** The type of formulas in the solver. The list of free arguments in quantifiers
    is a bit tricky, and used mainly for skolemization, so you should probably
    not touch it. (TODO: further explanations in full doc?). *)

type t_order =
  | Same
  | Inverse

val t_order : t_order Tag.t
(** Tags containing information about the order of arguments for equalities. *)

type 'a order =
  | F of 'a
  | L of 'a order list

type f_order = formula order

val f_order : f_order Tag.t
(** Tags containing information about the inital order of arfuments for the
    [And] and [Or] constructions. *)

type valuation =
  | Assign of (term -> term)
  | Eval of (term -> term list * (unit -> term)) (**)
(** Terms can be given a value by two mutually exclusive process:
    either a value can be assigned to the term, or the term can be evaluated
    given the assignemtns of subterms. *)

(** {3 Exceptions} *)

exception Type_mismatch of term * ty * ty
(* Raised when as Type_mismatch(term, actual_type, expected_type) *)

exception Bad_arity of (ttype, ty) function_descr id * ty list * term list
exception Bad_ty_arity of (unit, ttype) function_descr id * ty list
(** Raised when trying to build an application with wrong arity *)

exception Cannot_valuate of term
(** Raised when requesting an assigner/interpreter for a variable, but none has been set. *)

(** {2 Printing} *)

module Print : sig
  (** Pretty printing functions *)

  val name : Pretty.name tag
  (** The name tag is used for the printing of identifiers.
      When an identifier has an name tag, its value is used instead of the
      identifier intrinsic name. *)

  val pos : Pretty.pos tag
  (** Positioning for pretty printing. If this tag is set, the printing functions
      will ignore type arguments (for readability).
      [Pretty.Infix] uses the identifier as a separator when printing th argument list
      [Pretty.Prefix] just ignore type arguments. *)

  val id : Format.formatter -> 'a id -> unit
  val id_ty : Format.formatter -> ty id -> unit
  val id_ttype : Format.formatter -> ttype id -> unit

  val const_ty : Format.formatter -> (ttype, ty) function_descr id -> unit
  val const_ttype : Format.formatter -> (unit, ttype) function_descr id -> unit

  val meta : Format.formatter -> 'a meta -> unit
  val meta_ty : Format.formatter -> ty meta -> unit
  val meta_ttype : Format.formatter -> ttype meta -> unit

  val ty : Format.formatter -> ty -> unit
  val fun_ty : Format.formatter -> (ttype, ty) function_descr -> unit

  val ttype : Format.formatter -> ttype -> unit
  val fun_ttype : Format.formatter -> (unit, ttype) function_descr -> unit

  val term : Format.formatter -> term -> unit
  val formula : Format.formatter -> formula -> unit
end

(** {2 Status} *)

module Status : sig

  type t = status

  val print : Format.formatter -> t -> unit

  val goal : t
  val hypothesis : t
  (** Standard status for goals (theorem/lemmas to prove), and hypothesis (assumptions) repectly.
      Unless otherwise specified, types and terms have hypothesis status. *)
end

(** {2 Identifiers & Metas} *)

module Id : sig

  include Sig.PolyFull with type 'a t = 'a id
  (** Base signature for parametric types. *)

  module Ty : Sig.Full with type t = ty id
  module Ttype : Sig.Full with type t = ttype id
  module Const : Sig.Full with type t = (ttype, ty) function_descr id
  module TyCstr : Sig.Full with type t = (unit, ttype) function_descr id
  (** Concrete instances for functor application. *)

  val get_tag : _ id -> 'a tag -> 'a option
  (** Get a tag value from an identifier. *)

  val tag : _ id -> 'a tag -> 'a -> unit
  (** Add a tag to an id. *)

  val cached : ('a id -> 'b) -> 'a id -> 'b
  (** Cache a computation on ids. *)

  val prop : (unit, ttype) function_descr id
  val base : (unit, ttype) function_descr id
  (** Constants representing the type for propositions and a default type
      for term, respectively. *)

  val mk_new : ?builtin:builtin -> ?tags:tag_map -> string -> 'a -> 'a id
  (** Generic function to create new ids. You should not use this function
      to create ids used in regular terms, but rather for ids used
      in other term structures (for isntance proof terms). *)

  val ttype : ?builtin:builtin -> ?tags:tag_map -> string -> ttype id
  (** Create a fresh type variable with the given name. *)

  val ty : ?builtin:builtin -> ?tags:tag_map -> string -> ty -> ty id
  (** Create a fresh variable with given name and type *)

  val ty_fun :
    ?builtin:builtin -> ?tags:tag_map ->
    string -> int -> (unit, ttype) function_descr id
  (** Create a fresh type constructor with given name and arity *)

  val term_fun :
    ?builtin:builtin -> ?tags:tag_map ->
    string -> ttype id list -> ty list -> ty -> (ttype, ty) function_descr id
  (** [term_fun name type_vars arg_types return_type] returns a fresh constant symbol,
      possibly polymorphic with respect to the variables in [type_vars] (which may appear in the
      types in [arg_types] and in [return_type]). *)

  val ty_skolem : ttype id -> (unit, ttype) function_descr id
  val term_skolem : ty id -> (ttype, ty) function_descr id
  (** Returns the skolem symbols associated with the given variables. The skolems
      symbols take as arguments the free_variables of their defining formula.
      For simplicity, just apply the skolem to the free_args of the quantified expression. *)

  val occurs_in_term : ty id -> term -> bool
  (** Returns [true] if the given variable occurs in the term. *)

  val set_valuation : 'a id -> int -> valuation -> unit
  (** [set_eval v n k] sets [k] as the valuation to call in order to
      give a value to a term that has [v] as top-level symbol,
      using priority [n].
      (only the valuation with highest priority is called). *)

  val is_valuated : 'a id -> bool
  (** Has the given id's valuation been set ? *)

  val is_assignable : 'a id -> bool
  (** Has an assignment function been set for the given id ? *)

  val merge_fv :
    ttype id list * ty id list ->
    ttype id list * ty id list ->
    ttype id list * ty id list
  (** Merge lists of free variables *)

  val remove_fv :
    ttype id list * ty id list ->
    ttype id list * ty id list ->
    ttype id list * ty id list
  (** [remove_fv l l'] remove variables that belong to [l'] from [l]. *)

  val inter_fv :
    ttype id list * ty id list ->
    ttype id list * ty id list ->
    ttype id list * ty id list
  (** [inter_fv l l'] remove variables that belong to [l'] from [l]. *)
end

module Meta : sig

  include Sig.PolyFull with type 'a t = 'a meta
  (** Base interface *)

  module Ty : Sig.Full with type t = ty meta
  module Ttype : Sig.Full with type t = ttype meta
  (** Convenience modules *)

  val def : meta_index -> formula
  (** Returns the formula associated with a given meta index. *)

  val of_index : meta_index -> ttype meta list * ty meta list
  (** Returns the list of all metas sharing the given index. *)

  val occurs_in_term : ty meta -> term -> bool
  (** Returns [true] if the given meta-variable occurs in the term. *)

  val merge_fm :
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list
  (** Merge lists of free meta-variables *)

  val remove_fm :
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list
  (** [remove_fm l l'] removes from l all meta appearing in [l']. *)

  val inter_fm :
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list ->
    ttype meta list * ty meta list
  (** [inter_fm l l'] removes from l all meta appearing in [l']. *)

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

  val apply : ?status:status -> (unit, ttype) function_descr id -> ty list -> ty
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

  val cached : (ty -> 'a) -> (ty -> 'a)
  (** Cache a computaiton using a fresh tag. *)

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

  val apply : ?status:status -> (ttype, ty) function_descr id -> ty list -> term list -> term
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

  val valuation : term -> valuation
  (** Return a valuation for the given term
      @raise (Cannot_valuate t) if there is no valuation *)

  val tag : term -> 'a tag -> 'a -> unit
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : term -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

  val cached : (term -> 'a) -> (term -> 'a)
  (** Cache a computaiton using a fresh tag. *)

end

(** {2 Formulas} *)

module Formula : sig

  include Sig.Full with type t = formula

  type var_subst = (ty id, formula) Subst.t
  type meta_subst = (ty meta, formula) Subst.t
  (** The type of substitutions in types. *)

  val f_true : formula
  val f_false : formula
  (** Formula for the true and false constants *)

  val eq : ?status:status -> term -> term -> formula
  (** Create an equality over two terms. The two given terms
      must have the same type [t], which must be different from {!Ty.prop} *)

  val pred : ?status:status -> term -> formula
  (** Create a formula from a term. The given term must have type {!Ty.prop} *)

  val neg : ?status:status -> formula -> formula
  (** Returns the negation of the given formula *)

  val f_and : ?status:status -> formula list -> formula
  (** Returns the conjunction of the given formulas *)

  val f_or : ?status:status -> formula list -> formula
  (** Returns the disjunction of the given formulas *)

  val imply : ?status:status -> formula -> formula -> formula
  (** [imply p q] returns a formula representing [p] implies [q]. *)

  val equiv : ?status:status -> formula -> formula -> formula
  (** [equi p q] returns a formula representing [p] equivalent to [q] *)

  val all : ?status:status -> ttype id list * ty id list -> formula -> formula
  (** Universally quantify the given formula over the given variables *)

  val ex : ?status:status -> ttype id list * ty id list -> formula -> formula
  (** Existentially quantify the given formula over the given variables *)

  val subst :
    ?fix:bool ->
    ?ty_var_map:Ty.var_subst ->
    ?ty_meta_map:Ty.meta_subst ->
    ?t_var_map:Term.var_subst ->
    ?t_meta_map:Term.meta_subst ->
    ?f_var_map:var_subst ->
    ?f_meta_map:meta_subst ->
    formula -> formula
  (** Substitution over formulas
      @param fix wther to fixpoint the substitution application *)

  val partial_inst : Ty.var_subst -> Term.var_subst -> formula -> formula
  (** Make a partial instanciation of the given formula with the substitutions. *)

  val gen_metas : formula -> ttype meta list * ty meta list
  (** Given a formula [f] which is either a universal quantification over terms,
      or the negation of an existencial quantification over terms,
      returns a list of meta-variables associated with [f]. *)

  val fv : formula -> ttype id list * ty id list
  val fm : formula -> ttype meta list * ty meta list
  (** Return the list of free variables or metas in the given formula. *)

  val tag : formula -> 'a tag -> 'a -> unit
  (** Insert a local type in the given type. Does not change the semantic
      value of the type. Can be used to store some additional user-defined
      information. *)

  val get_tag : formula -> 'a tag -> 'a option
  (** Returns the local data associated with the given tag, if if exists *)

end

