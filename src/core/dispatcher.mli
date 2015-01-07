
include Msat.Plugin_intf.S
  with type term = Expr.term and type formula = Expr.formula

exception Absurd of formula list (* To be used by extensions in 'assume' *)
exception Extension_not_found of string

type extension = {
  name : string;
  assume : slice -> unit;
  assign : term -> term option;
  eval : term -> (bool * int) option;
  interprets : Expr.ty Expr.function_descr Expr.var -> bool;
  backtrack : int -> unit;
  current_level : unit -> int;
}

val activate : string -> unit
val register : extension -> unit

