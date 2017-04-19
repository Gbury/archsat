
(* Mapping over variables & meta-variables

   This module defines mapping from variables and meta-variables to
   types and terms.
*)


(** {2 Type definition and usual functions} *)

type t
(** Abstract type for mappings *)

val hash : t -> int
(** Hash over mappings *)

val compare : t -> t -> int
(** Comparison over bindings *)

val equal : t -> t -> bool
(** Equality for mappings *)

val print : Format.formatter -> t -> unit
(** Pretty printer for mappings *)


(** {2 Mapping manipulation} *)

val empty : t
(** The empty mapping *)

val is_empty : t -> bool
(** Is the mapping empty. *)

val fixpoint : t -> t
(** Compute the fixpoint of a mapping.
    WARNING: may not terminate if mapping contains cycles. *)

val map : (Expr.ty -> Expr.ty) -> (Expr.term -> Expr.term)  -> t -> t
(** Map some functions over the types and terms used in the mapping. *)

val exists :
  ?ty_var:(Expr.Id.Ttype.t -> Expr.ty -> bool) ->
  ?ty_meta:(Expr.Meta.Ttype.t -> Expr.ty -> bool) ->
  ?term_var:(Expr.Id.Ty.t -> Expr.term -> bool) ->
  ?term_meta:(Expr.Meta.Ty.t -> Expr.term -> bool) ->
  t -> bool
(** Is there a binding that satisfies the given predicate ? *)

val for_all :
  ?ty_var:(Expr.Id.Ttype.t -> Expr.ty -> bool) ->
  ?ty_meta:(Expr.Meta.Ttype.t -> Expr.ty -> bool) ->
  ?term_var:(Expr.Id.Ty.t -> Expr.term -> bool) ->
  ?term_meta:(Expr.Meta.Ty.t -> Expr.term -> bool) ->
  t -> bool
(** Do all the bindings verify the given predicates ? *)

(** {2 Mapping application} *)

val apply_ty : fix:bool -> t -> Expr.ty -> Expr.ty
val apply_term : fix:bool -> t -> Expr.term -> Expr.term
(** Aplly a mapping to a type or term. The [~fix] parameter indicates
    wether the mapping application should be recursive or not: for instance,
    given a mapping [t] whichs binds [x] to [y] and [y] to [a]:
    - [apply_term ~fix:false t x == y]
    - [apply_term ~fix:true t x == a]
*)

(** {2 Variable bindings} *)

module Var : sig

  val mem_ty : t -> Expr.Id.Ttype.t -> bool
  val mem_term : t -> Expr.Id.Ty.t -> bool
  (** Does the given identifier is mapped ? *)

  val get_ty : t -> Expr.Id.Ttype.t -> Expr.ty
  val get_term : t -> Expr.Id.Ty.t -> Expr.term
  (** Get the value mapped to an identiier in the mapping.
      @raise Not_found if the identifier is not bound. *)

  val get_ty_opt : t -> Expr.Id.Ttype.t -> Expr.ty option
  val get_term_opt : t -> Expr.Id.Ty.t -> Expr.term option
  (** Get the value mapped to an identifier in hte mapping. *)

  val bind_ty : t -> Expr.Id.Ttype.t -> Expr.ty -> t
  val bind_term : t -> Expr.Id.Ty.t -> Expr.term -> t
  (** Add a new binding to the mapping.
      Will overwrite any previously existing binding. *)

end


(** {2 Meta-variable bindings} *)

module Meta : sig

  val mem_ty : t -> Expr.Meta.Ttype.t -> bool
  val mem_term : t -> Expr.Meta.Ty.t -> bool
  (** Does the given identifier is mapped ? *)

  val get_ty : t -> Expr.Meta.Ttype.t -> Expr.ty
  val get_term : t -> Expr.Meta.Ty.t -> Expr.term
  (** Get the value mapped to an identiier in the mapping.
      @raise Not_found if the identifier is not bound. *)

  val get_ty_opt : t -> Expr.Meta.Ttype.t -> Expr.ty option
  val get_term_opt : t -> Expr.Meta.Ty.t -> Expr.term option
  (** Get the value mapped to an identifier in hte mapping. *)

  val bind_ty : t -> Expr.Meta.Ttype.t -> Expr.ty -> t
  val bind_term : t -> Expr.Meta.Ty.t -> Expr.term -> t
  (** Add a new binding to the mapping.
      Will overwrite any previously existing binding. *)

end

