
let section = Section.make "proving"

module P = Solver.Proof

(* Small wrapper *)
(* ************************************************************************ *)

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

(* Proof introduction *)
(* ************************************************************************ *)

let init opt () =
  pp_opt Coq.init Options.(opt.proof.coq) opt;
  pp_opt Dot.init_full Options.(opt.proof.full_dot) opt;
  ()

(* Proof hyps *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Dolmen.Id)

(* mutable state *)
let goals = ref []

let add_goal id =
  begin match !goals with
    | [] -> ()
    | _ -> Util.warn ~section "%s%s"
             "Multiple goals are not very well supported,@ "
             "please consider having a single goal at any time"
  end;
  goals := id :: !goals

let get_goals () = !goals

let clear_goals () = goals := []

(* Some wrappers *)
(* ************************************************************************ *)

(* Wrapper to get implicitly typed identifiers. *)
let wrapper t tr =
  let l = ref [] in
  let callback = Some (function id -> l := id :: !l) in
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
  let id = Expr.Id.mk_new v.Expr.id_name ty in
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

(* Hyp&Goal declarations *)
(* ************************************************************************ *)

let declare_hyp_aux opt id =
  pp_opt Coq.declare_hyp Options.(opt.coq) id;
  ()

let declare_hyp opt id f =
  let implicit, t = wrapper f Term.of_formula in
  let p = Term.declare (Dolmen.Id.full_name id) t in
  let () = declare_implicits opt implicit in
  if Options.(opt.context) then declare_hyp_aux opt p;
  p

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

(* Resolution helpers *)
(* ************************************************************************ *)

let resolve =
  let coq = Proof.Last_but_not_least, (fun fmt st ->
      ()
    ) in
  let compute seq () =
    (), [| |]
  in
  let elaborate st args = assert false in
  Proof.mk_step ~coq ~compute ~elaborate

(* Computing a full resolution proof *)
(* ************************************************************************ *)

type _ Dispatcher.msg +=
  | Lemma : Dispatcher.lemma_info -> Proof.proof Dispatcher.msg

let introduce_hyp id l pos =
  pos
  |> Logic.cut "C" (Logic.clause_type l)
    ~f:(fun p -> p
                 |> Logic.introN "Ax" (List.length l)
                 |> Logic.or_elim id ~f:Logic.absurd)

let compute_aux pos node =
  match node.P.step with
  | P.Hypothesis ->
    Util.debug ~section "Introducing clause: %a" P.St.print_clause node.P.conclusion;
    let id = Solver.hyp_proof node.P.conclusion in
    let l = List.map (fun a ->
        Term.of_formula a.P.St.lit
      ) (P.to_list node.P.conclusion) in
    introduce_hyp id l pos
  | _ -> pos

let compute opt p =
  let g =
    match get_goals () with
    | [] -> Term.false_term
    | [ g ] -> g.Expr.id_type
    | h :: r ->
      let aux a b = Term.apply Term.or_term [a; b.Expr.id_type] in
      List.fold_left aux h.Expr.id_type  r
  in
  let seq = Proof.mk_sequent Proof.Env.empty g in
  let proof = Proof.mk seq in
  let () =
    let init = Proof.(pos (root proof)) in
    try
      let final = P.fold compute_aux init p in
      if not (Logic.trivial final) then begin
        Util.error ~section "Proof incomplete";
      end
    with Proof.Failure (msg, _) ->
      Util.warn ~section "@[<hv>Error during proof building:@ %s@\n%s"
        msg "Try and look at the full-dot output to see the incomplete proof"
  in
  proof

(* Output proofs *)
(* ************************************************************************ *)

let pp_proof_lazy lang pp o x =
  match o with
  | None -> ()
  | Some fmt ->
    begin try
        pp fmt (Lazy.force x)
      with Proof.Open_proof ->
        Util.warn ~section "Printed an open proof for language '%s'" lang
    end

let output_proof opt p =
  let () = pp_opt Unsat_core.print Options.(opt.unsat_core) p in
  let () = pp_opt Dot.print Options.(opt.res_dot) p in
  let p' = lazy (compute opt p) in
  let () = pp_proof_lazy "coq" (Proof.print ~lang:Proof.Coq) Options.(opt.coq) p' in
  let () = pp_proof_lazy "full-dot" (Proof.print ~lang:Proof.Dot) Options.(opt.full_dot) p' in
  ()



