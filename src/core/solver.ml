
let section = Dispatcher.solver_section

(* Msat instanciation *)
(* ************************************************************************ *)

module S = Msat.Internal.Make(Dispatcher.SolverTypes)(Dispatcher.SolverTheory)()

(* Proof replay helpers *)
(* ************************************************************************ *)

type model = unit -> (Expr.term * Expr.term) list

type proof = S.Proof.proof

type res =
  | Sat of model
  | Unsat of proof
  | Unknown

(* Proof replay helpers *)
(* ************************************************************************ *)

type unsat_ret =
  | Unsat_ok

type sat_ret =
  | Sat_ok
  | Assume of Expr.formula list

type _ Dispatcher.msg +=
  | Found_sat : model -> sat_ret Dispatcher.msg
  | Found_unsat : proof -> unsat_ret Dispatcher.msg
  | Found_unknown : unit -> unit Dispatcher.msg

(* Solving module *)
(* ************************************************************************ *)

let if_sat acc = function
  | None -> acc
  | Some Sat_ok -> acc
  | Some Assume l ->
    begin match acc with
      | None -> Some l
      | Some l' -> Some (l @ l')
    end

let rec solve_aux ?(assumptions = []) () =
  match begin
    let () = S.pop () in
    let () = S.push () in
    let () = S.local assumptions in
    let () = S.solve () in
    Util.debug ~section 1 "Found SAT";
    let model = Dispatcher.model in
    Dispatcher.handle if_sat None (Found_sat model)
  end with
  | None -> Sat Dispatcher.model
  | Some assumptions ->
    solve_aux ~assumptions ()
  | exception S.Unsat ->
    let proof =
      match S.unsat_conflict () with
      | None -> assert false
      | Some c -> S.Proof.prove_unsat c
    in
    Unsat proof

let solve () =
  Util.enter_prof section;
  let res = solve_aux () in
  Util.exit_prof section;
  res

let assume l =
  Util.enter_prof section;
  let l = List.map (List.map Dispatcher.pre_process) l in
  List.iter (fun cl -> Util.debug ~section 1 "Assuming : %a"
                (CCPrint.list ~sep:"; " Expr.Debug.formula) cl) l;
  let () = S.assume l in
  Util.exit_prof section


