
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

(* hyps *)
let hyps = ref []

let add_hyp id = hyps := id :: !hyps

let get_hyps () = !hyps

(* goals *)
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
  let () = add_hyp p in
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

let resolve_step =
  let coq = Proof.Last_but_not_least, (fun fmt (id, t) ->
      Format.fprintf fmt "@[<hv 2>pose proof (@,%a@;<0,-2>) as %a.@]"
        Coq.Print.term t Coq.Print.id id
    ) in
  let compute seq (c, c', res) =
    let t = Logic.resolve_clause c c' res in
    let e = Proof.env seq in
    let e' = Proof.Env.prefix e "R" in
    let e'' = Proof.Env.intro e' t in
    (Proof.Env.find e'' t, t), [| Proof.mk_sequent e'' (Proof.goal seq) |]
  in
  let elaborate (id, t) = function
    | [| body |] -> Term.letin id t body
    | _ -> assert false
  in
  Proof.mk_step ~coq ~compute ~elaborate "resolve"

let resolve pos c c' res =
  match Proof.apply_step pos resolve_step (c, c', res) with
  | (id, _), [| pos' |] -> id, pos'
  | _ -> assert false

(* Computing a full resolution proof *)
(* ************************************************************************ *)

type _ Dispatcher.msg +=
  | Lemma : Dispatcher.lemma_info -> (Proof.pos, unit) Proof.tactic Dispatcher.msg

let introduce_hyp id l pos =
  pos
  |> Logic.cut "C" (Logic.clause_type l)
    ~f:(fun p -> p
                 |> Logic.introN "Ax" (List.length l)
                 |> Logic.or_elim id ~f:Logic.absurd)

let introduce_lemma f l pos =
  pos |> Logic.cut "L" (Logic.clause_type l) ~f

let compute_aux h pos node =
  let l = List.map (fun a ->
      Term.of_formula a.P.St.lit
    ) (P.to_list node.P.conclusion) in
  let id, pos' =
    match node.P.step with
    | P.Assumption -> assert false
    | P.Hypothesis ->
      Util.debug ~section "Introducing clause: %a" P.St.print_clause node.P.conclusion;
      let id = Solver.hyp_proof node.P.conclusion in
      introduce_hyp id l pos
    | P.Lemma lemma ->
      Util.debug ~section "Proving lemma: %a" P.St.print_clause node.P.conclusion;
      let f =
        match Dispatcher.(ask lemma.plugin_name (Lemma lemma.proof_info)) with
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
      resolve pos left_id right_id l
    | _ ->
      raise (Proof.Failure ("incomplete resolution proof reconstruction", Logic.extract_open pos))
  in
  let () = P.H.add h node.P.conclusion id in
  pos'

let compute opt p =
  let h = P.H.create 4013 in
  let g =
    match get_goals () with
    | [] -> Term.false_term
    | [ g ] -> g.Expr.id_type
    | h :: r ->
      let aux a b = Term.apply Term.or_term [a; b.Expr.id_type] in
      List.fold_left aux h.Expr.id_type  r
  in
  let env = List.fold_left Proof.Env.declare Proof.Env.empty (get_hyps ()) in
  let seq = Proof.mk_sequent env g in
  let proof = Proof.mk seq in
  let () =
    let init = Proof.(pos (root proof)) in
    try
      let final = P.fold (compute_aux h) init p in
      if not (Logic.trivial final) then begin
        Util.error ~section "Proof incomplete";
      end
    with Proof.Failure (msg, _) ->
      Util.warn ~section "Error during proof building:@.%s" msg;
      Util.warn "Try and look at the full-dot output to see the incomplete proof"
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



