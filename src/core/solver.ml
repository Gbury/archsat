
let section = Dispatcher.solver_section

(* Solving module *)
(* ************************************************************************ *)

module Smt = Msat.Internal.Make(struct
    let debug i format = Util.debug ~section i format
  end)(Dispatcher.SolverTypes)(Dispatcher.SolverTheory)

module Dot = Msat.Dot.Make(Smt.Proof)(struct
    let clause_name c = c.Dispatcher.SolverTypes.name
    let print_atom = Dispatcher.SolverTypes.print_atom
    let lemma_info p =
      let name, color, t_args, f_args = Dispatcher.proof_debug p in
      name, color,
      List.map (fun t -> (fun fmt () -> Expr.Print.term fmt t)) t_args @
      List.map (fun f -> (fun fmt () -> Expr.Print.formula fmt f)) f_args
  end)

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

let print_dot_proof = Dot.print


