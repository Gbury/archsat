
let section = Section.make ~parent:Proof.section "proving"

let proof_section = Section.make ~parent:Proof.section "generation"
let elaboration_section = Section.make ~parent:section "elaboration"
let normalisation_section = Section.make ~parent:section "normalisation"

let dot_section = Section.make ~parent:section "dot_print"
let coq_section = Section.make ~parent:section "coq_print"
let coqterm_section = Section.make ~parent:section "coqterm_print"
let coqterm_norm_section = Section.make ~parent:section "coqterm-norm_print"

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
        CCOpt.iter (Util.info ~section "Printing proof for %s") lang;
        Util.enter_prof s;
        pp fmt p;
        Util.exit_prof s
      with
      | Proof.Open_proof ->
        Util.exit_prof s;
        Util.warn ~section "Found an open proof !"
      | exn ->
        Util.exit_prof s;
        raise exn
    end

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
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq.term_norm) id;
  ()

let declare_implicits opt = function
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
  pp_opt Coq.init Options.(opt.proof.coq.script) opt;
  pp_opt Coq.init Options.(opt.proof.coq.term) opt;
  pp_opt Coq.init Options.(opt.proof.coq.term_norm) opt;
  pp_opt Dot.init_full Options.(opt.proof.dot.full) opt;
  ()

(* Hyp declarations *)
(* ************************************************************************ *)

let declare_hyp_aux ?loc opt id =
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq.term_norm) id;
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
  pp_opt (Coq.declare_goal ?loc) Options.(opt.coq.script) id;
  pp_opt (Coq.declare_goal_term ?loc) Options.(opt.coq.term) id;
  pp_opt (Coq.declare_goal_term ?loc) Options.(opt.coq.term_norm) id;
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
  pp_lazy None coqterm_norm_section Options.(opt.coq.term_norm) proof
    (Proof.print_term_preludes ~lang:Proof.Coq);
  ()

(* Output proofs *)
(* ************************************************************************ *)

let print_context context proof_context print fmt proof =
  let pp = if context then proof_context print else print in
  pp fmt proof

let output_proof opt p =
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
  (* Lazily compute the proof *)
  let proof = lazy (
    Util.info ~section "Computing proof";
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
    let res = Resolution.compute opt seq (sid, p) in
    Util.exit_prof proof_section;
    res
  ) in
  let term = lazy (
    let p = Lazy.force proof in
    Util.info ~section "Computing proof term";
    Util.enter_prof elaboration_section;
    let t = Proof.elaborate p in
    Util.exit_prof elaboration_section;
    p, t
  ) in
  let norm = lazy (
    let p, t = Lazy.force term in
    Util.info ~section "Computing normalized proof term";
    Util.enter_prof normalisation_section;
    let t' = Term.reduce t in
    let () = Term.disambiguate t' in
    Util.exit_prof normalisation_section;
    p, t'
  ) in
  (* Declare the prelues for term printing *)
  if Options.(opt.context) then declare_term_preludes opt proof;
  (* Declare the goal *)
  if Options.(opt.context) then declare_goal_aux ?loc opt gid;
  (* Print the lazy proof in coq *)
  let () = pp_lazy (Some "coq") coq_section Options.(opt.coq.script) proof
      (print_context opt.Options.context Coq.proof_context
         (Proof.print ~lang:Proof.Coq)) in
  (* Print the lazy proof term in coq *)
  let () = pp_lazy (Some "coqterm") coqterm_section Options.(opt.coq.term) term
      (print_context opt.Options.context Coq.proof_term_context
         (Proof.print_term ~big:false ~lang:Proof.Coq)) in
  (* Print the normalized lazy proof term in coq *)
  let () = pp_lazy (Some "coqterm-normalize") coqterm_norm_section Options.(opt.coq.term_norm) norm
      (print_context opt.Options.context Coq.proof_term_context
         (Proof.print_term ~big:true ~lang:Proof.Coq)) in
  (* Print the lazy proof in dot *)
  let () = pp_lazy (Some "dot") dot_section Options.(opt.dot.full) proof
      (print_context true Dot.proof_context
         (Proof.print ~lang:Proof.Dot)) in
  (* Done ! exit the profiling section, ^^ *)
  ()



