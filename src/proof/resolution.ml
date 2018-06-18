
let section = Section.make ~parent:Solver.proof_section "res"

module P = Solver.Proof

(* Introducing lemmas *)
(* ************************************************************************ *)

let introduce_lemma f l pos =
  pos |> Logic.cut ~weak:true "L" (Logic.clause_type l) ~f

(* Introducing hyp as weak clauses *)
(* ************************************************************************ *)

let introduce_hyp t l pos =
  pos |> Logic.cut ~weak:true "C" (Logic.clause_type l)
    ~f:(fun p -> p
                 |> Logic.introN "Ax" (List.length l)
                 |> Logic.or_elim t ~f:Logic.absurd)

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

(* Incremental dot printing *)
(* ************************************************************************ *)

let h = Hashtbl.create 13

let print_incr_dot_aux file proof =
  let out = open_out file in
  let fmt = Format.formatter_of_out_channel out in
  let () = Dot.proof_context (Proof.print ~lang:Proof.Dot) fmt proof in
  close_out out

let print_incr_dot opt proof =
  match Options.(opt.incr_dot) with
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
      Util.debug ~section "Proving lemma: %a" P.St.print_clause node.P.conclusion;
      let f =
        match Dispatcher.(ask lemma.plugin_name (Proof.Lemma lemma.proof_info)) with
        | Some f -> f
        | None -> (fun _ -> ())
      in
      introduce_lemma f l pos
    | P.Resolution (left, right, _) ->
      let left_proof = P.expand left in
      let right_proof = P.expand right in
      Util.debug ~section "Performing resolution between: %s-%s -> %s"
        left_proof.P.conclusion.P.St.name right_proof.P.conclusion.P.St.name
        node.P.conclusion.P.St.name;
      let left_id = P.H.find h (P.expand left).P.conclusion in
      let right_id = P.H.find h (P.expand right).P.conclusion in
      Logic.resolve left_id right_id l pos
    | _ ->
      raise (Proof.Failure ("incomplete resolution proof reconstruction", Logic.extract_open pos))
  in
  Util.debug ~section "%s -> %a" node.P.conclusion.P.St.name Expr.Id.print id;
  let () = P.H.add h node.P.conclusion id in
  pos'

let compute opt seq p =
  let h = P.H.create 4013 in
  let proof = Proof.mk seq in
  let () =
    let init = Proof.(pos (root proof)) in
    try
      let final = P.fold (fun acc node ->
          print_incr_dot opt proof;
          compute_aux h acc node
        ) init p in
      if not (Logic.trivial final) then begin
        Util.error ~section "Proof incomplete";
      end
    with Proof.Failure (msg, _) ->
      Util.warn ~section "Error during proof building:@.%s" msg;
  in
  proof

