
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

(* Solving *)
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

(* Model output *)
let model = Smt.model

let full_model = Dispatcher.model

(* Proof output *)
type proof = Smt.Proof.proof

let get_proof () =
  Smt.Proof.learn (Smt.history ());
  match Smt.unsat_conflict () with
  | None -> assert false
  | Some c -> Smt.Proof.prove_unsat c

let print_proof_dot = Smt.Proof.print_dot


