
exception Not_unifiable

val unify : (Expr.term * Expr.term) list -> Expr.term -> Expr.term -> Unif.t list
(** Unify two term given a set of equations. *)

