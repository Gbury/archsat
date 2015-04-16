
val unify : ?max_depth: int ->
  (Expr.term * Expr.term) list ->
  (Unif.t -> unit) ->
  Expr.term -> Expr.term -> unit
(** Unify two term given a set of equations. *)

