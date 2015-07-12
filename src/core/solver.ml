
let section = Util.Section.make "solver"

(* Wrapper around expressions *)
(* ************************************************************************ *)

module SatExpr = struct

  module Term = Expr.Term
  module Formula = Expr.Formula

  let dummy = Expr.Formula.f_true

  let fresh () = assert false

  let neg f = Expr.Formula.neg f

  let norm = function
    | { Expr.formula = Expr.False } -> Expr.Formula.f_true, true
    | { Expr.formula = Expr.Not f } -> f, true
    | f -> f, false
end

(* Dispatcher *)
(* ************************************************************************ *)

module SatPlugin = Dispatcher

(* Solving module *)
(* ************************************************************************ *)

module Smt = Msat.Mcsolver.Make(struct
    let debug i format = Util.debug ~section i format
  end)(SatExpr)(SatPlugin)

(* Solving *)
type res = Sat | Unsat

let solve () =
  Util.enter_prof section;
  let res = match Smt.solve () with
    | () -> Sat
    | exception Smt.Unsat -> Unsat
  in
  Util.exit_prof section;
  res

let assume l =
  Util.enter_prof section;
  let l = List.map (List.map Dispatcher.pre_process) l in
  List.iter (fun cl -> Util.debug ~section 1 "Assuming : %a"
                (CCPrint.list ~sep:"; " Expr.Debug.formula) cl) l;
  begin match Smt.assume l with
    | () -> ()
    | exception Smt.Unsat -> ()
  end;
  Util.exit_prof section

(* Model output *)
let model = Smt.model

let full_model = Dispatcher.model

(* Proof output *)
type proof = Smt.Proof.proof

let get_proof () =
  match Smt.unsat_conflict () with
  | None -> assert false
  | Some c -> Smt.Proof.prove_unsat c

let print_dot_proof = Smt.Proof.print_dot


