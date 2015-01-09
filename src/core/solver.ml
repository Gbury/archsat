
(* Wrapper around expressions *)
(* ************************************************************************ *)

module SatExpr = struct

  module Term = Expr.Term
  module Formula = Expr.Formula

  let dummy = Expr.f_true

  let fresh () = assert false

  let neg f = Expr.f_not f

  let norm = function
    | { Expr.formula = Expr.Not f } -> f, true
    | f -> f, false
end

(* Dispatcher *)
(* ************************************************************************ *)

module SatPlugin = Dispatcher

(* Solving module *)
(* ************************************************************************ *)

module Smt = Msat.Mcsolver.Make(SatExpr)(SatPlugin)

type res = Sat | Unsat

let _i = ref 0

let solve () =
  try
    Smt.solve ();
    Sat
  with Smt.Unsat -> Unsat

let assume l =
  incr _i;
  try
    Smt.assume l !_i
  with Smt.Unsat -> ()

let model = Smt.model

let full_model = Dispatcher.model

