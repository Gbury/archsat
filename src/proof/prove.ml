
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

let add_goal id =
  match !goal with
  | None ->
    goal := Some id
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

(* Wrapper to get implicitly typed identifiers. *)
let wrapper t tr =
  let l = ref [] in
  let callback = Some (fun id ->
    Util.debug ~section "Found implicitly typed constant: %a"
      Expr.Id.print id;
    l := id :: !l
    ) in
  let res = tr ?callback t in
  !l, res

let print_id_typed fmt id =
  Format.fprintf fmt "%a: @[<hov>%a@]"
    Expr.Print.id id Term.print id.Expr.id_type

(* Declare identifiers *)
let declare_id_aux opt id =
  pp_opt Coq.declare_id Options.(opt.coq) id;
  ()

let declare_implicits opt l =
  if Options.(opt.context) then begin
    List.iter (declare_id_aux opt) (List.rev l)
  end else begin match l with
    | [] -> ()
    | _ ->
      Util.warn ~section
        "@[<hv 2>The following identifiers are implicitly typed:@ @[<v>%a@]@]"
        CCFormat.(list ~sep:(return "@ ") print_id_typed) l
  end

(* Identifier declarations *)
(* ************************************************************************ *)

(* Print type declarations for ids *)
let declare_id opt implicit v ty =
  Util.debug ~section "Declaring %a" Expr.Print.id v;
  let id = Term.declare v.Expr.id_name ty in
  let () = Term.trap_id v id in
  let () = declare_implicits opt implicit in
  if Options.(opt.context) then declare_id_aux opt id

(* Declare type consructors *)
let declare_ty opt v =
  Util.debug ~section "Translating %a" Expr.Print.id v;
  let implicit, ty = wrapper v.Expr.id_type
      (Term.of_function_descr Term.of_unit Term.of_ttype)
  in
  declare_id opt implicit v ty

(* Declare term constants *)
let declare_term opt v =
  Util.debug ~section "Translating %a" Expr.Print.id v;
  let implicit, ty = wrapper v.Expr.id_type
      (Term.of_function_descr Term.of_ttype Term.of_ty)
  in
  declare_id opt implicit v ty

(* Proof initialization *)
(* ************************************************************************ *)

let init opt () =
  pp_opt Coq.init Options.(opt.proof.coq) opt;
  pp_opt Dot.init_full Options.(opt.proof.full_dot) opt;
  ()

(* Hyp declarations *)
(* ************************************************************************ *)

let declare_hyp_aux opt id =
  pp_opt Coq.declare_hyp Options.(opt.coq) id;
  ()

let declare_hyp opt id f =
  let implicit, t = wrapper f Term.of_formula in
  let p = Term.declare (Dolmen.Id.full_name id) t in
  let () = declare_implicits opt implicit in
  let () = add_hyp p in
  if Options.(opt.context) then declare_hyp_aux opt p;
  p

(* Goal declarations *)
(* ************************************************************************ *)

let declare_goal_aux opt id =
  pp_opt Coq.declare_goal Options.(opt.coq) id;
  ()

let declare_goal opt id f =
  let implicit, t = wrapper f Term.of_formula in
  let p = Term.declare (Dolmen.Id.full_name id) t in
  let () = declare_implicits opt implicit in
  let () = add_goal p in
  if Options.(opt.context) then declare_goal_aux opt p;
  p

let implicit_goal opt =
  let p = Term.declare "implicit_goal" Term.false_term in
  if not Options.(opt.context) then
    Util.warn ~section "Using an implicit goal with context, this might be a problem"
  else begin
    declare_goal_aux opt p
  end;
  p

(* Output proofs *)
(* ************************************************************************ *)

let print_context context proof_context print fmt proof =
  let pp = if context then proof_context print else print in
  pp fmt proof

let pp_proof_lazy lang o x pp =
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
  let g = (* get the current goal *)
    let p =
      match get_goal () with
      | None -> implicit_goal opt
      | Some g -> g
    in
    p.Expr.id_type
  in
  (* Lazily compute the proof *)
  let p' = lazy (
    let hyps = get_hyps () in
    let env = List.fold_left Proof.Env.declare Proof.Env.empty hyps in
    let seq = Proof.mk_sequent env g in
    Resolution.compute opt seq p
  ) in
  (* Print the lazy proof in each language. *)
  let () = pp_proof_lazy "coq" Options.(opt.coq) p'
      (print_context opt.Options.context Coq.proof_context (Proof.print ~lang:Proof.Coq)) in
  let () = pp_proof_lazy "full-dot" Options.(opt.full_dot) p'
      (print_context true Dot.proof_context (Proof.print ~lang:Proof.Dot)) in
  ()



