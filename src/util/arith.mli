
module M : Map.S with type key = Expr.term

module Mod : sig

  type t

  val congr : Z.t -> Z.t -> t
  val merge : t -> t -> t option

  val sum_up : t -> Z.t * Z.t

end

module Lit : sig
  type t = {
    const : Builtin.Arith.value;
    sum : Q.t M.t;
  }

  val const : Builtin.Arith.value -> t
  val monome : Q.t -> Expr.term -> t

  val add : t -> t -> t
  val diff : t -> t -> t
  val times : Builtin.Arith.value -> t -> t

  val parse_num : Expr.term -> t option
end
