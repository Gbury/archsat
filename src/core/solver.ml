
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

module S = struct
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

  (*
  let get_proof () =
    Smt.Proof.learn (Smt.history ());
    match Smt.unsat_conflict () with
    | None -> assert false
    | Some c -> Smt.Proof.prove_unsat c

  let unsat_core = Smt.Proof.unsat_core
  *)

end
