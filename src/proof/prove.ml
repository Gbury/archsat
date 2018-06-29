
let section = Section.make ~parent:Solver.proof_section "proving"

module P = Solver.Proof

(* Small wrapper *)
(* ************************************************************************ *)

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

(* Proof hyps *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Dolmen.Id)

(* hyps *)
let hyps = ref []

let add_hyp id = hyps := id :: !hyps

let get_hyps () = !hyps

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
  pp_opt (Coq.declare_id ?loc) Options.(opt.coq) id;
  pp_opt (Coq.declare_id ?loc) Options.(opt.coqterm) id;
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
  pp_opt Coq.init Options.(opt.proof.coq) opt;
  pp_opt Coq.init Options.(opt.proof.coqterm) opt;
  pp_opt Dot.init_full Options.(opt.proof.full_dot) opt;
  ()

(* Hyp declarations *)
(* ************************************************************************ *)

let declare_hyp_aux ?loc opt id =
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coq) id;
  pp_opt (Coq.declare_hyp ?loc) Options.(opt.coqterm) id;
  ()

let declare_hyp ?loc opt id implicit p =
  let () = declare_implicits opt implicit in
  let () = add_hyp p in
  if Options.(opt.context) then declare_hyp_aux ?loc opt p

(* Goal declarations *)
(* ************************************************************************ *)

let declare_goal_aux ?loc opt id =
  pp_opt (Coq.declare_goal ?loc) Options.(opt.coq) id;
  pp_opt (Coq.declare_goal_term ?loc) Options.(opt.coqterm) id;
  ()

let declare_goal ?loc opt id implicit (solver_id, p) =
  let () = declare_implicits opt implicit in
  let () = add_goal (solver_id, p) in
  if Options.(opt.context) then declare_goal_aux ?loc opt p

let implicit_goal opt =
  let p = Term.declare "implicit_goal" Term.false_term in
  if not Options.(opt.context) then
    Util.warn ~section "Using an implicit goal without context, this might be a problem"
  else begin
    declare_goal_aux opt p
  end;
  p

(* Output proofs *)
(* ************************************************************************ *)

let print_context context proof_context print fmt proof =
  let pp = if context then proof_context print else print in
  pp fmt proof

let pp_lazy lang o x pp =
  match o with
  | None -> ()
  | Some fmt ->
    begin try
        pp fmt (Lazy.force x)
      with Proof.Open_proof ->
        Util.warn ~section "Printed an open proof for language '%s'" lang
    end

let output_proof opt p =
  (* Simple proofs *)
  let () = pp_opt Unsat_core.print Options.(opt.unsat_core) p in
  let () = pp_opt Dot.print Options.(opt.res_dot) p in
  (* More complex proofs *)
  let sid, g = (* get the current goal *)
    let sid, p =
      match get_goal () with
      | None -> None, implicit_goal opt
      | Some (sid, g) -> Some sid, g
    in
    sid, p.Expr.id_type
  in
  (* Lazily compute the proof *)
  let proof = lazy (
    let hyps = get_hyps () in
    let env = List.fold_left Proof.Env.declare Proof.Env.empty hyps in
    let seq = Proof.mk_sequent env g in
    Resolution.compute opt seq (sid, p)
  ) in
  (* Print the lazy proof in each language. *)
  let () = pp_lazy "coq" Options.(opt.coq) proof
      (print_context opt.Options.context Coq.proof_context (Proof.print ~lang:Proof.Coq)) in
  let () = pp_lazy "coqterm" Options.(opt.coqterm) proof
      (print_context opt.Options.context Coq.proof_term_context (Proof.print_term ~lang:Proof.Coq)) in
  let () = pp_lazy "full-dot" Options.(opt.full_dot) proof
      (print_context true Dot.proof_context (Proof.print ~lang:Proof.Dot)) in
  ()



