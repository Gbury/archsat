
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

(* Wrapper around dispatcher *)
(* ************************************************************************ *)

module SatPlugin = struct

    (* Type definitions *)
    type term = Expr.term
    type formula = Expr.formula
    type proof = unit

    type assumption =
      | Lit of formula
      | Assign of term * term

    type slice = {
      start : int;
      length : int;
      get : int -> assumption * int;
      push : formula list -> proof -> unit;
    }

    type level = unit

    type res =
        | Sat of level
        | Unsat of formula list * proof

    type eval_res =
        | Valued of bool * int
        | Unknown


    (* Functions and valued *)
    let dummy = ()
    let current_level () = ()

    let assume s = Sat (current_level ())

    let backtrack () = ()

    let assign t = assert false

    let iter_assignable f p = ()

    let eval f = Unknown

end

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
