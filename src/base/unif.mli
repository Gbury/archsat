
(** Unification for terms *)

type subst
val bindings : subst -> (Expr.ty Expr.meta * Expr.term) list

exception Not_unifiable

(** {2 Robinson unification} *)

val unify_simple : Expr.term -> Expr.term -> subst
val cached_unify : Expr.term -> Expr.term -> subst

