
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

module Smt = Msat.Mcsolver.Make(struct let debug = Debug.log end)(SatExpr)(SatPlugin)

(* Pre-processing *)

let check_var v =
    if not (Expr.is_interpreted v) && not (Expr.is_assignable v) then
        Debug.log 0 "WARNING: Variable %a is neither interpreted nor assignable" Expr.debug_var v

let rec check_term = function
    | { Expr.term = Expr.Var v } -> check_var v
    | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_var)
    | { Expr.term = Expr.Tau t } -> check_var Expr.(t.tau_var)
    | { Expr.term = Expr.App (p, _, l)} ->
      check_var p;
      List.iter check_term l

let rec check = function
  | { Expr.formula = Expr.Equal (a, b) } ->
          check_term a;
          check_term b
  | { Expr.formula = Expr.Pred p } ->
          check_term p
  | { Expr.formula = ( Expr.True | Expr.False ) } ->
          ()
  | { Expr.formula = Expr.Not f } ->
          check f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
          List.iter check l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
          check p;
          check q
  | { Expr.formula = Expr.All (_, f) }
  | { Expr.formula = Expr.AllTy (_, f) }
  | { Expr.formula = Expr.Ex (_, f) } ->
          check f

let preprocess f =
    SatPlugin.preprocess f;
    check f

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


