
let section = Dispatcher.solver_section

(* Module instanciation *)
(* ************************************************************************ *)

module S = Msat.Internal.Make
    (Dispatcher.SolverTypes)
    (Dispatcher.SolverTheory)
    ()

module Dimacs = Msat.Dimacs.Make
    (Dispatcher.SolverTypes)
    ()

(* Problem export *)
(* ************************************************************************ *)

let export_dimacs fmt () =
  let hyps = S.hyps () in
  let history = S.history () in
  let local = S.temp () in
  Dimacs.export fmt ~hyps ~history ~local

let export_icnf fmt () =
  let hyps = S.hyps () in
  let history = S.history () in
  let local = S.temp () in
  Dimacs.export_icnf fmt ~hyps ~history ~local

(* Type definitions *)
(* ************************************************************************ *)

type model = (Expr.term * Expr.term) list
(** The type of models for first order problems *)

type view = (Expr.formula -> unit) -> unit
(** A view of the trail when SAT is reached. *)

type proof = S.Proof.proof
(** A proof of UNSAT. *)

type res =
  | Sat of model
  | Unsat of proof
  | Unknown

(* Messages *)
(* ************************************************************************ *)

type unsat_ret =
  | Unsat_ok

type sat_ret =
  | Sat_ok
  | Restart
  | Incomplete
  | Assume of Expr.formula list

type _ Dispatcher.msg +=
  | Restarting : unit Dispatcher.msg
  | Found_sat : view -> sat_ret Dispatcher.msg
  | Found_unsat : proof -> unsat_ret Dispatcher.msg
  | Found_unknown : unit -> unit Dispatcher.msg

(* Solving module *)
(* ************************************************************************ *)

let if_sat_iter s f =
  let open Msat.Plugin_intf in
  for i = s.start to s.start + s.length - 1 do
    match s.get i with
    | Lit g -> f g
    | _ -> ()
  done

(* Priority of extensions instructions:
   Sat_ok < Incomplete < Assume _ < Restart
   We are interested in computing the maximum during folding.
*)
let if_sat acc res =
  match acc, res with
  (* Neutral case *)
  | _, (None | Some Sat_ok) -> acc
  (* Incompleteness is stronger than sat_ok, but weaker than everything else *)
  | Sat_ok, Some Incomplete -> Incomplete
  | _, Some Incomplete -> acc
  (* When encountering assume, we want to merge the assume lists if possible *)
  | Assume l', Some Assume l -> Assume (l @ l')
  | (Sat_ok | Incomplete), Some ((Assume _) as r) -> r
  | Restart, Some Assume _ -> Restart
  (* Restart is stronger than everything *)
  | _, Some Restart -> Restart

let report ?export status =
  Util.log ~section "Found %s" status;
  begin match export with
  | None -> ()
  | Some fmt -> export_icnf fmt ()
  end

let rec solve_aux
    ?export
    ?(check_model=false)
    ?(check_proof=false)
    ?(assumptions = [])
    () =
  match begin
    Util.info ~section "Preparing solver";
    let () = S.pop () in
    let () = S.push () in
    let () = S.local assumptions in
    Util.log ~section "Solving problem";
    S.solve ()
  end with
  | () ->
    report ?export "SAT";
    if check_model then begin
      if S.check () then
        Util.info ~section "SAT model checked"
      else
        Util.error ~section "Invalid SAT model"
    end;
    let view = if_sat_iter (S.full_slice ()) in
    begin match Dispatcher.handle if_sat Sat_ok (Found_sat view) with
      | Incomplete ->
        Unknown
      | Sat_ok ->
        Sat (Dispatcher.model ())
      | Restart ->
        Util.info ~section "Restarting...";
        Dispatcher.send Restarting;
        solve_aux ?export ~check_model ~check_proof ()
      | Assume assumptions ->
        Util.info ~section "New assumptions:@ @[<hov>%a@]"
          CCFormat.(list ~sep:(return " &&@ ") Expr.Print.formula) assumptions;
        solve_aux ?export ~check_model ~check_proof ~assumptions ()
    end
  | exception S.Unsat ->
    report ?export "UNSAT";
    let proof =
      match S.unsat_conflict () with
      | None -> assert false
      | Some c -> S.Proof.prove_unsat c
    in
    if check_proof then begin
      Util.info "Checking UNSAT proof...";
      S.Proof.check proof
    end;
    Unsat proof

let solve ?check_model ?check_proof ?export () =
  Util.enter_prof section;
  let res =
    try
      solve_aux ?check_model ?check_proof ?export ()
    with
    | Extension.Abort (ext, msg) ->
      Util.warn ~section "Extension '%s' aborted proof search with message:@\n%s" ext msg;
      Unknown
  in
  Util.exit_prof section;
  res

let assume l =
  Util.enter_prof section;
  let l = List.map (List.map Dispatcher.pre_process) l in
  Util.info ~section "@[<hov 2>New local assumptions:@ @[<hov>%a@]"
    CCFormat.(
         hovbox (list ~sep:(return " &&@ ")
           (hovbox (list ~sep:(return " ||@ ") Expr.Print.formula))
       )) l;
  let () = S.assume l in
  Util.exit_prof section

let add_atom = S.new_atom

(* Proof manipulation *)
(* ************************************************************************ *)

module Proof = S.Proof

(* Model manipulation *)
(* ************************************************************************ *)

module Model = struct

  type t = model

  let rec print_aux fmt = function
    | [] -> ()
    | (u, v) :: r ->
      Format.fprintf fmt "%a -> %a@\n"
        Expr.Term.print u Expr.Term.print v;
      print_aux fmt r

  let print fmt l =
    Format.fprintf fmt "@[<hov 2>Model:@\n%a@]" print_aux l


end

