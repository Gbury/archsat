
let section = Dispatcher.solver_section

type res = Sat | Unsat

(* Proof replay helpers *)
(* ************************************************************************ *)

exception Restart

type ret =
  | Ok
  | Toggle of string

type _ Dispatcher.msg += Found : res option -> ret Dispatcher.msg

let do_pre = function
  | Ok -> ()
  | Toggle ext -> Dispatcher.Plugin.deactivate ext

let do_post = function
  | Ok -> ()
  | Toggle ext -> Dispatcher.Plugin.activate ext

(* Solving module *)
(* ************************************************************************ *)

module Smt = Msat.Internal.Make(struct
    let debug i format = Util.debug ~section i format
  end)(Dispatcher.SolverTypes)(Dispatcher.SolverTheory)

module Dot = Msat.Dot.Make(Smt.Proof)(struct
    let print_atom = Dispatcher.SolverTypes.print_atom
    let lemma_info p =
      let name, color, t_args, f_args = Dispatcher.proof_debug p in
      name, color,
      List.map (fun t -> (fun fmt () -> Expr.Print.term fmt t)) t_args @
      List.map (fun f -> (fun fmt () -> Expr.Print.formula fmt f)) f_args
  end)

(* Solving *)
type level = Smt.level

let solve_aux () =
  match Smt.solve () with
  | () -> Some Sat
  | exception Smt.Unsat -> Some Unsat
  | exception Restart -> None

let rec solve () =
  Util.enter_prof section;
  let lvl = Smt.push () in
  let res = solve_aux () in
  let s = Stack.create () in
  Dispatcher.handle (fun ret () -> Stack.push ret s) () (Found res);
  let res' =
    if not (Stack.is_empty s) then begin
      Smt.pop lvl;
      Stack.iter do_pre s;
      let tmp = solve () in
      Stack.iter do_post s;
      tmp
    end else res
  in
  Util.exit_prof section;
  res'

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

(* Push/Pop options *)
let push = Smt.push

let pop = Smt.pop

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


