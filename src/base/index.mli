
(** Index on terms for fast unification.
    This module implements indexing on terms in order
    to have fast access to unifiable terms stored in the index.
    Currently mainly used in *)

(** {2 Basic Index} *)

module Make(T: Set.OrderedType) : sig

  type t

  val empty : t

  val add : section:Util.Section.t -> Expr.term -> T.t -> t -> t

  val remove : section:Util.Section.t -> Expr.term -> T.t -> t -> t

  val find_unify : section:Util.Section.t -> Expr.term -> t -> (Expr.term * Unif.t * T.t list) list

  val find_match : section:Util.Section.t -> Expr.term -> t -> (Expr.term * Unif.Match.tt * T.t list) list

end
