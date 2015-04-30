
module type S = sig
  type t
  type expr

  val root : t
  val arg : int -> t -> t

  val compare : t -> t -> int

  val apply : t -> expr -> expr
  val substitute : t -> expr -> expr -> expr
  val fold : ('a -> t -> expr -> 'a) -> 'a -> expr -> 'a
end

module Ty : sig
  include S with type expr = Expr.ty
end

module Term : sig
  include S with type expr = Expr.term
end
