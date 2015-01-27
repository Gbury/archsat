
(** Unification for terms *)

type subst

(** {2 Robinson unification} *)

val unify_simple : Expr.term -> Expr.term -> subst


