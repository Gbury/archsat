(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Proof.section "printing"

let proof_section = Section.make ~parent:Proof.section "msat-res"
let script_section = Section.make ~parent:Proof.section "generation"
let elaboration_section = Section.make ~parent:Proof.section "elaboration"
let normalisation_section = Section.make ~parent:Proof.section "normalisation"

let dot_section = Section.make ~parent:section "dot_print"
let msat_section = Section.make ~parent:section "coq-msat_print"
let coqscript_section = Section.make ~parent:section "coqscript_print"
let coqterm_section = Section.make ~parent:section "coqterm_print"
let coqnorm_section = Section.make ~parent:section "coqnorm_print"
let dkterm_section = Section.make ~parent:section "dkterm_print"
let dknorm_section = Section.make ~parent:section "dknorm_print"

module P = Solver.Proof

exception Hypothesis_name_conflict of
    (Term.id * Dolmen.ParseLocation.t option) *
    (Term.id * Dolmen.ParseLocation.t option)

(* Small wrapper *)
(* ************************************************************************ *)

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

let pp_lazy lang s o x pp =
  match o with
  | None -> ()
  | Some fmt ->
    begin try
        let p = Lazy.force x in
        CCOpt.iter (Util.log ~section "Printing proof for %s") lang;
        Util.enter_prof s;
        Format.fprintf fmt "%a@." pp p;
        CCOpt.iter (Util.info ~section "Finished printing proof for %s") lang;
        Util.exit_prof s
      with
      | Proof.Open_proof ->
        Util.exit_prof s;
        Util.warn ~section "Found an open proof !"
      | exn ->
        Util.exit_prof s;
        raise exn
    end

(* Global  *)
(* ************************************************************************ *)

let global_implicits = ref []

let add_implicit c =
  global_implicits := c :: !global_implicits

let get_global_implicits () =
  let l = !global_implicits in
  global_implicits := [];
  l

(* Proof hyps *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Dolmen.Id)
module M = Hashtbl.Make(struct
    type t = Term.id
    let hash = Expr.Id.hash
    let equal = Expr.Id.equal
  end)

(* hyps *)
let hyps = ref []
let hyp_locs = M.create 113

let add_hyp ?loc id =
  M.add hyp_locs id loc;
  hyps := id :: !hyps

let get_hyps () = !hyps

let get_hyp_loc h =
  try M.find hyp_locs h
  with Not_found -> None

(* goals *)
let goal = ref None

let add_goal x =
  match !goal with
  | None ->
    goal := Some x
  | Some _ ->
    Util.error ~section "%s%s"
      "Multiple goals are not supported in proof output,@ "
      "please consider having a single goal at any time"

let get_goal () =
  let res = !goal in
  goal := None;
  res

(* Some wrappers *)
(* ************************************************************************ *)

let print_id_typed fmt id =
  Format.fprintf fmt "%a: @[<hov>%a@]"
    Expr.Print.id id Term.print id.Expr.id_type

(* Declare identifiers *)
let declare_id_aux ?loc opt id =
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.msat) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.norm) id;
  pp_opt (Dedukti.declare_id ?loc) Options.(opt.dedukti.term) id;
  pp_opt (Dedukti.declare_id ?loc) Options.(opt.dedukti.norm) id;
  ()

let declare_implicits opt l =
  match (get_global_implicits () @ l) with
  | [] -> ()
  | l ->
    if Options.(opt.context) then begin
      List.iter (declare_id_aux opt) l
    end else begin
      Util.warn ~section
        "@[<hv 2>The following identifiers are implicitly typed:@ @[<v>%a@]@]"
        CCFormat.(list ~sep:(return "@ ") print_id_typed) l
    end

(* Identifier declarations *)
(* ************************************************************************ *)

(* Print type declarations for ids *)
let declare_id ?loc opt implicit id =
  Util.debug ~section "Declaring %a" Expr.Print.id id;
  let () = declare_implicits opt implicit in
  if Options.(opt.context) then declare_id_aux ?loc opt id

(* Proof initialization *)
(* ************************************************************************ *)

let init opt () =
  pp_opt Coq.init Options.(opt.proof.coq.msat) opt;
  pp_opt Coq.init Options.(opt.proof.coq.script) opt;
  pp_opt Coq.init Options.(opt.proof.coq.term) opt;
  pp_opt Coq.init Options.(opt.proof.coq.norm) opt;
  pp_opt Dedukti.init Options.(opt.proof.dedukti.term) opt;
  pp_opt Dedukti.init Options.(opt.proof.dedukti.norm) opt;
  pp_opt Dot.init_full Options.(opt.proof.dot.full) opt;
  ()

(* Hyp declarations *)
(* ************************************************************************ *)

let declare_hyp_aux ?loc opt id =
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.msat) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.norm) id;
  pp_opt (Dedukti.declare_hyp ?loc) Options.(opt.dedukti.term) id;
  pp_opt (Dedukti.declare_hyp ?loc) Options.(opt.dedukti.norm) id;
  ()

let declare_hyp ?loc opt id implicit p =
  Util.debug ~section "@[<hv 2>Declaring hyp@ %a :@ %a@]"
    Expr.Id.print p Term.print p.Expr.id_type;
  let () = declare_implicits opt implicit in
  let () = add_hyp ?loc p in
  if Options.(opt.context) then declare_hyp_aux ?loc opt p

(* Goal declarations *)
(* ************************************************************************ *)

let declare_goal_aux ?loc opt id =
  pp_opt (Coq.declare_goal ?loc) Options.(opt.coq.msat) id;
  pp_opt (Coq.declare_goal ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_goal_term ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_goal_term ?loc) Options.(opt.coq.norm) id;
  pp_opt (Dedukti.declare_goal_term ?loc) Options.(opt.dedukti.term) id;
  pp_opt (Dedukti.declare_goal_term ?loc) Options.(opt.dedukti.norm) id;
  ()

let declare_goal ?loc opt id implicit (solver_id, p) =
  Util.debug ~section "@[<hv 2>Registering goal@ %a :@ %a@]"
    Expr.Id.print p Term.print p.Expr.id_type;
  let () = declare_implicits opt implicit in
  let () = add_goal (loc, solver_id, p) in
  ()

let implicit_goal opt =
  let p = Term.declare "implicit_goal" Term.false_term in
  if not Options.(opt.context) then
    Util.warn ~section "Using an implicit goal without context, this might be a problem";
  p

(* Prelude printing (for terms) *)
(* ************************************************************************ *)

let declare_term_preludes opt proof =
  pp_lazy None coqterm_section Options.(opt.coq.term) proof
    (Proof.print_term_preludes ~lang:Proof.Coq);
  pp_lazy None coqnorm_section Options.(opt.coq.norm) proof
    (Proof.print_term_preludes ~lang:Proof.Coq);
  pp_lazy None dkterm_section Options.(opt.dedukti.term) proof
    (Proof.print_term_preludes ~lang:Proof.Dedukti);
  pp_lazy None dkterm_section Options.(opt.dedukti.norm) proof
    (Proof.print_term_preludes ~lang:Proof.Dedukti);
  ()

(* Output proofs *)
(* ************************************************************************ *)

let print_context context proof_context print fmt proof =
  let pp = if context then proof_context print else print in
  pp fmt proof

let output_proof opt p =
  (* Declare evantual implicits generated during rpof search *)
  let () = declare_implicits opt [] in
  (* Simple proofs *)
  let () = pp_opt Unsat_core.print Options.(opt.unsat_core) p in
  let () = pp_opt Dot.print Options.(opt.dot.res) p in
  (* More complex proofs *)
  let loc, sid, gid =
    match get_goal () with
    | None -> None, None, implicit_goal opt
    | Some (loc, sid, g) -> loc, Some sid, g
  in
  let g = gid.Expr.id_type in
  (* Lazuly compute the proof using the msat backend *)
  let proof = lazy (
    Util.log ~section "Computing proof";
    Util.enter_prof proof_section;
    let hyps = get_hyps () in
    let env =
      try
        List.fold_left Proof.Env.declare Proof.Env.empty hyps
      with Proof.Env.Conflict (h, h') ->
        raise (Hypothesis_name_conflict ((h, get_hyp_loc h),
                                         (h', get_hyp_loc h')))
    in
    let seq = Proof.mk_sequent env g in
    let res = Resolution.msat_backend opt seq (sid, p) in
    Util.exit_prof proof_section;
    res
  ) in
  (* Lazily compute the script *)
  let script = lazy (
    Util.log ~section "Computing script";
    Util.enter_prof script_section;
    let hyps = get_hyps () in
    let env =
      try
        List.fold_left Proof.Env.declare Proof.Env.empty hyps
      with Proof.Env.Conflict (h, h') ->
        raise (Hypothesis_name_conflict ((h, get_hyp_loc h),
                                         (h', get_hyp_loc h')))
    in
    let seq = Proof.mk_sequent env g in
    let res = Resolution.compute opt seq (sid, p) in
    Util.exit_prof script_section;
    res
  ) in
  (* Lazily compute the script term *)
  let term = lazy (
    let p = Lazy.force script in
    Util.log ~section "Computing proof term";
    Util.enter_prof elaboration_section;
    let t = Proof.elaborate p in
    Util.exit_prof elaboration_section;
    p, t
  ) in
  (* Lazily compute the script normalized term *)
  let norm = lazy (
    let p, t = Lazy.force term in
    Util.log ~section "Computing normalized proof term";
    Util.enter_prof normalisation_section;
    let t' = Term.reduce t in
    Util.exit_prof normalisation_section;
    p, t'
  ) in
  (* Declare the prelues for term printing *)
  if Options.(opt.context) then declare_term_preludes opt script;
  (* Declare the goal *)
  if Options.(opt.context) then declare_goal_aux ?loc opt gid;
  (* Print the lazy proof in coq *)
  let () = pp_lazy (Some "coq") msat_section Options.(opt.coq.msat) proof
      (print_context opt.Options.context Coq.proof_context
         (Proof.print ~lang:Proof.Coq)) in
  (* Print the lazy script in coq *)
  let () = pp_lazy (Some "coqscript") coqscript_section Options.(opt.coq.script) script
      (print_context opt.Options.context Coq.proof_context
         (Proof.print ~lang:Proof.Coq)) in
  (* Print the lazy proof term in coq *)
  let () = pp_lazy (Some "coqterm") coqterm_section Options.(opt.coq.term) term
      (print_context opt.Options.context Coq.proof_term_context
         (Proof.print_term ~big:Options.(opt.coq.term_big) ~lang:Proof.Coq)) in
  (* Print the lazy proof term in dedukti *)
  let () = pp_lazy (Some "dkterm") dkterm_section Options.(opt.dedukti.term) term
      (print_context opt.Options.context Dedukti.proof_term_context
         (Proof.print_term ~big:Options.(opt.dedukti.term_big) ~lang:Proof.Dedukti)) in
  (* Print the normalized lazy proof term in coq *)
  let () = pp_lazy (Some "coqnorm") coqnorm_section Options.(opt.coq.norm) norm
      (print_context opt.Options.context Coq.proof_term_context
         (Proof.print_term ~big:Options.(opt.coq.norm_big) ~lang:Proof.Coq)) in
  (* Print the normalized lazy proof term in dedukti *)
  let () = pp_lazy (Some "dknorm") dknorm_section Options.(opt.dedukti.norm) norm
      (print_context opt.Options.context Dedukti.proof_term_context
         (Proof.print_term ~big:Options.(opt.dedukti.norm_big) ~lang:Proof.Dedukti)) in
  (* Print the lazy script in dot *)
  let () = pp_lazy (Some "dot") dot_section Options.(opt.dot.full) script
      (print_context true Dot.proof_context
         (Proof.print ~lang:Proof.Dot)) in
  (* Done ! exit the profiling section, ^^ *)
  ()



