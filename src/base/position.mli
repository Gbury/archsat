
type t

type 'a res =
  | Var
  | Top of 'a Expr.function_descr Expr.id
  | Possible
  | Impossible

val root : t
val arg : int -> t -> t

val compare : t -> t -> int

module Ty : sig
  val apply : t -> Expr.ty -> Expr.ttype res * Expr.ty option
  val substitute : t -> by:Expr.ty -> Expr.ty -> Expr.ty option
  val fold : ('a -> t -> Expr.ty -> 'a) -> 'a -> Expr.ty -> 'a
  val find_map : (t -> Expr.ty -> 'a option) -> Expr.ty -> 'a option
end

module Term : sig
  val apply : t -> Expr.term -> Expr.ty res * Expr.term option
  val substitute : t -> by:Expr.term -> Expr.term -> Expr.term option
  val fold : ('a -> t -> Expr.term -> 'a) -> 'a -> Expr.term -> 'a
  val find_map : (t -> Expr.term -> 'a option) -> Expr.term -> 'a option
end
