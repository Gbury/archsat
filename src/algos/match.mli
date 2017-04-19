
(** Matching on expressions *)

exception Impossible_ty of Expr.ty * Expr.ty
exception Impossible_term of Expr.term * Expr.term

val ty : Mapping.t -> Expr.ty -> Expr.ty -> Mapping.t
val term : Mapping.t -> Expr.term -> Expr.term -> Mapping.t
(** [ty pat t] tries and match [pat] with the type [t].
    [term pat t] tries and match [pat] with the term [t].
    @raise Impossible_ty if the pattern does not match a type.
    @raise Impossible_term if the pattern does not match a term. *)

val find : section:Section.t -> Expr.term -> Expr.term -> Mapping.t option
(** [find ~section pat term] try and find a substitution [u] such that
    [Mapping.apply_term ~fix:false u pat = term]. *)




