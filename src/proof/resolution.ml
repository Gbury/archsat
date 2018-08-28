(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Proof.section "res"

module P = Solver.Proof

(* Introducing lemmas *)
(* ************************************************************************ *)

let introduce_lemma f l pos =
  pos |> Logic.cut "L" (Logic.clause_type l) ~f

(* Introducing hyp as weak clauses *)
(* ************************************************************************ *)

let prove_hyp t l pos =
  pos
  |> Logic.introN "Ax" (List.length l)
  |> begin match l with
    | [ t' ] -> Logic.absurd t'
    | _ -> Logic.or_elim t ~f:Logic.absurd
  end

let introduce_hyp t l pos =
  pos |> Logic.cut "C" (Logic.clause_type l) ~f:(prove_hyp t l)

(* From mSAT lit to proof term *)
(* ************************************************************************ *)

let term_of_atom a =
  let lit = P.St.(a.var.pa.lit) in
  let pos = P.St.(a.var.pa == a) in
  if Expr.Formula.equal lit Expr.Formula.f_true then begin
    if pos then
      Term.true_term
    else
      Term.false_term
  end else begin
    let t = Term.of_formula lit in
    if pos then t
    else Term.app Term.not_term t
  end

(* Get function for proving lemmas *)
(* ************************************************************************ *)

let prove_function lemma clause =
  let name = lemma.Dispatcher.plugin_name in
  let p_name = lemma.Dispatcher.proof_name in
  let section = Dispatcher.find_section name in
  Util.debug ~section "Proving lemma (%s.%s): %a" name p_name P.St.print_clause clause;
  match Dispatcher.(ask name (Proof.Lemma lemma.proof_info)) with
  | Some f -> (fun pos -> f (Proof.switch section pos))
  | None -> (fun _ -> ())

(* Incremental dot printing *)
(* ************************************************************************ *)

let h = Hashtbl.create 13

let print_incr_dot_aux file proof =
  let out = open_out file in
  let fmt = Format.formatter_of_out_channel out in
  let () = Dot.proof_context (Proof.print ~lang:Proof.Dot) fmt proof in
  close_out out

let print_incr_dot opt proof =
  match Options.(opt.dot.incr) with
  | None -> ()
  | Some prefix ->
    let n = try Hashtbl.find h prefix with Not_found -> 0 in
    let () = Hashtbl.add h prefix (n + 1) in
    let file = Format.asprintf "%s.%03d.gv" prefix n in
    print_incr_dot_aux file proof

(* Compute a formal proof from a resolution proof *)
(* ************************************************************************ *)

let compute_aux h pos node =
  let l = List.map term_of_atom (P.to_list node.P.conclusion) in
  let id, pos' =
    match node.P.step with
    | P.Assumption -> assert false
    | P.Hypothesis ->
      Util.debug ~section "Introducing clause: %a" P.St.print_clause node.P.conclusion;
      let t = Term.id (Solver.hyp_proof node.P.conclusion) in
      Util.debug ~section "  using %a" Term.print t;
      introduce_hyp t l pos
    | P.Lemma lemma ->
      let f = prove_function lemma node.P.conclusion in
      introduce_lemma f l pos
    | P.Resolution (left, right, _) ->
      let left_proof = P.expand left in
      let right_proof = P.expand right in
      Util.debug ~section "Performing resolution between: %s-%s -> %s"
        left_proof.P.conclusion.P.St.name right_proof.P.conclusion.P.St.name
        node.P.conclusion.P.St.name;
      let left_id = P.H.find h left_proof.P.conclusion in
      let right_id = P.H.find h right_proof.P.conclusion in
      Logic.resolve left_id right_id l pos
    | P.Duplicate (c, _) ->
      let proof = P.expand c in
      Util.debug ~section "Eliminating duplicates in: %s -> %s"
        proof.P.conclusion.P.St.name node.P.conclusion.P.St.name;
      let proof_id = P.H.find h proof.P.conclusion in
      Logic.remove_duplicates proof_id l pos
  in
  Util.debug ~section "%s -> %a" node.P.conclusion.P.St.name Expr.Id.print id;
  let () = P.H.add h node.P.conclusion id in
  pos'

let compute_final h pos proof =
  let node = P.expand proof in
  let id = P.H.find h node.P.conclusion in
  Logic.exact [] (Term.id id) pos

let compute opt seq (sid, p) =
  let h = P.H.create 4013 in
  let proof = Proof.mk seq in
  let () =
    let handle id =
       match sid with
         | Some sid -> Solver.register_goal sid id
         | None ->
           Util.error ~section "No solver_id provided for binding to goal introduction"
    in
    let init = Logic.nnpp ~handle @@ Proof.(pos (root proof)) |> Proof.switch section in
    try
      let final = P.fold (fun acc node ->
          print_incr_dot opt proof;
          compute_aux h acc node
        ) init p in
      compute_final h final p;
    with
    | Proof.Failure (msg, pos) ->
      if Printexc.backtrace_status () then
        Printexc.print_backtrace stdout;
      Util.warn ~section "At proof position %a:@.%s" Proof.pp_pos pos msg
    | Proof.Env.Conflict (v, v') ->
      if Printexc.backtrace_status () then
        Printexc.print_backtrace stdout;
      Util.warn ~section "Conflict between two ids: %a <> %a" Expr.Print.id v Expr.Print.id v'
    | Proof.Env.Not_introduced t ->
      if Printexc.backtrace_status () then
        Printexc.print_backtrace stdout;
      Util.warn ~section "@[<hv>Formula was not introduced:@ %a@]" Term.print t
  in
  proof

(* Compute a formal proof from a resolution proof *)
(* ************************************************************************ *)

let msat_term_of_atom a =
  let lit = P.St.(a.var.pa.lit) in
  let pos = P.St.(a.var.pa == a) in
  let t = Term.of_formula lit in
  if pos then t else Term.app Term.not_term t

let pp_msat_coq pp_c =
  let module Arg = struct
    let prove_hyp = pp_c "hyp"
    let prove_lemma = pp_c "lemma"
    let prove_assumption = pp_c "assumption"
  end in
  let module M = Msat.Coq.Make(P)(Arg) in
  M.print

let msat_backend =
  let prelude (_, l, _) = l in
  let compute seq (h, p) =
    let env = Proof.env seq in
    let leafs = P.unsat_core p in
    Util.info ~section "Finished computing proof leafs";
    let preludes =
      List.fold_left (fun acc c ->
          let atoms = Array.to_list P.St.(c.atoms) in
          let l = List.map msat_term_of_atom atoms in
          let t = Logic.clause_type l in
          let proof = Proof.mk (Proof.mk_sequent env t) in
          let () = P.H.add h c proof in
          let pos = Proof.pos @@ Proof.root proof in
          let () =
            match P.St.(c.cpremise) with
            | P.St.Hyp ->
              let t' = Term.id (Solver.hyp_proof c) in
              Util.debug ~section "Proving hyp (%a) : %a" Term.print t' Term.print t;
              prove_hyp t' l pos
            | P.St.Lemma lemma ->
              let f = prove_function lemma c in
              f pos
            | P.St.Local | P.St.History _ -> assert false
          in
          Proof.preludes proof @ acc
        ) [] leafs
    in
    (h, preludes, p), [| |]
  in
  let coq = Proof.Last_but_not_least, (fun fmt (h, _, p) ->
      let pp_c status fmt name c =
        let atoms = Array.to_list P.St.(c.atoms) in
        let l = List.map msat_term_of_atom atoms in
        let t = Logic.clause_type l in
        let p = P.H.find h c in
        Format.fprintf fmt
          "@[<v>(* Proving %s: %s *)@ assert (%s : (@[<hov>%a@])).@ { @[<hov>%a@] }@ @]"
          status name name Coq.Print.term t (Proof.print ~prelude:false ~lang:Proof.Coq) p
      in
      pp_msat_coq pp_c fmt p
    ) in
  let elaborate _ _ = assert false in
  Proof.mk_step ~prelude ~coq ~elaborate ~compute "msat_coq_backend"

let msat_backend opt seq (sid, p) =
  let h = P.H.create 4013 in
  let proof = Proof.mk seq in
  let () =
    let handle id =
       match sid with
         | Some sid -> Solver.register_goal sid id
         | None ->
           Util.error ~section "No solver_id provided for binding to goal introduction"
    in
    let init = Logic.nnpp ~handle @@ Proof.(pos (root proof)) in
    let _, a = Proof.apply_step init msat_backend (h, p) in
    assert (Array.length a = 0)
  in
  proof

