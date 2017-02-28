
(** Matching on expressions *)

type t = {
  ty_map : (Expr.ttype Expr.id, Expr.ty) Expr.Subst.t;
  t_map : (Expr.ty Expr.id, Expr.term) Expr.Subst.t;
}
(** The type of unifiers. Used to represent subsitutions
    from variables to types or terms. *)

val empty : t
(** The empty substitution. *)

val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
(** Standard functions on substitutions. *)

val print : Format.formatter -> t -> unit
(** Substitution printers *)

val get_ty : t -> Expr.ttype Expr.id -> Expr.ty
val get_term : t -> Expr.ty Expr.id -> Expr.term
(** Accessors.
    @raise Not_found if no binding is found. *)

val get_ty_opt : t -> Expr.ttype Expr.id -> Expr.ty option
val get_term_opt : t -> Expr.ty Expr.id -> Expr.term option
(** Wrappers for accessors. *)

val mem_ty : t -> Expr.ttype Expr.id -> bool
val mem_term : t -> Expr.ty Expr.id -> bool
(** Test for existence of bindings *)

val bind_ty : t -> Expr.ttype Expr.id -> Expr.ty -> t
val bind_term : t -> Expr.ty Expr.id -> Expr.term -> t
(** Add new bindings. *)

val type_apply : t -> Expr.ty -> Expr.ty
val term_apply : t -> Expr.term -> Expr.term
val formula_apply : t -> Expr.formula -> Expr.formula
(** Apply a subsitution on variables. *)

exception Impossible_ty of Expr.ty * Expr.ty
exception Impossible_term of Expr.term * Expr.term

val ty : t -> Expr.ty -> Expr.ty -> t
val term : t -> Expr.term -> Expr.term -> t
(** [ty pat t] tries and match [pat] with the type [t].
    [term pat t] tries and match [pat] with the term [t].
    @raise Impossible_ty if the pattern does not match a type.
    @raise Impossible_term if the pattern does not match a term. *)

val find : section:Section.t -> Expr.term -> Expr.term -> t option
(** [find ~section pat term] try and find a substitution [u] such that
    [term_subst u pat = term]. *)




