
let section = Section.make ~parent:Proof.section "logic"

(* Logic preludes *)
(* ************************************************************************ *)

(* TODO: dispatch system for language-specific printing *)
let classical =
  Proof.Prelude.require (Expr.Id.mk_new "classical" ())
(* -> Coq.Logic.Classical *)

(* Useful constants *)
(* ************************************************************************ *)

let true_proof_id =
  Term.declare "I" Term.true_term

let true_proof =
  Term.id true_proof_id

let exfalso_id =
  let p = Term.var "P" Term._Prop in
  Term.declare "exfalso" (Term.forall p (
      Term.arrow Term.false_term (Term.id p)))

let nnpp_id =
  let p = Term.var "P" Term._Prop in
  let p_t = Term.id p in
  let nnp = Term.app Term.not_term (Term.app Term.not_term p_t) in
  Term.declare "NNPP" (Term.forall p (Term.arrow nnp p_t))

let and_elim_id, and_elim_alias =
  let a = Term.var "A" Term._Prop in
  let b = Term.var "B" Term._Prop in
  let p = Term.var "P" Term._Prop in
  let a_t = Term.id a in
  let b_t = Term.id b in
  let p_t = Term.id p in
  let a_and_b = Term.(apply and_term [a_t; b_t]) in
  let a_to_b_to_p = Term.arrows [a_t; b_t] p_t in
  let o = Term.var "o" a_and_b in
  let f = Term.var "f" a_to_b_to_p in
  let and_ind =
    Term.declare "and_ind"
      (Term.foralls [a; b; p] (
          Term.arrows [a_to_b_to_p; a_and_b]
            p_t
        )
      ) in
  let t =
    Term.lambdas [a; b; p; o; f] (
      Term.(apply (id and_ind) [a_t; b_t; p_t; id f; id o])
    ) in
  let id = Term.define "and_elim" t in
  id, Proof.Prelude.alias id t

let or_elim_id, or_elim_alias =
  let a = Term.var "A" Term._Prop in
  let b = Term.var "B" Term._Prop in
  let p = Term.var "P" Term._Prop in
  let a_t = Term.id a in
  let b_t = Term.id b in
  let p_t = Term.id p in
  let a_or_b = Term.(apply or_term [a_t; b_t]) in
  let a_to_p = Term.arrow a_t p_t in
  let b_to_p = Term.arrow b_t p_t in
  let o = Term.var "o" a_or_b in
  let f = Term.var "f" a_to_p in
  let g = Term.var "g" b_to_p in
  let or_ind =
    Term.declare "or_ind"
      (Term.foralls [a; b; p] (
          Term.arrows [a_to_p; b_to_p; a_or_b]
            p_t
        )
      ) in
  let t =
    Term.lambdas [a; b; p; o; f; g] (
      Term.(apply (id or_ind) [a_t; b_t; p_t; id f; id g; id o])
    ) in
  let id = Term.define "or_elim" t in
  id, Proof.Prelude.alias id t

let nnpp_term = Term.id nnpp_id
let exfalso_term = Term.id exfalso_id
let or_elim_term = Term.id or_elim_id
let and_elim_term = Term.id and_elim_id


(* Some generic tactic manipulations *)
(* ************************************************************************ *)

let extract_open pos =
  match Proof.extract @@ Proof.get pos with
  | Proof.Open sequent -> sequent
  | Proof.Proof _ -> assert false

let find t f pos =
  let seq = extract_open pos in
  let env = Proof.env seq in
  let id = Proof.Env.find env t in
  f id pos

(** Iterate a tactic n times *)
let rec iter tactic n pos =
  if n <= 0 then pos
  else iter tactic (n - 1) (tactic pos)

(* Standard tactics *)
(* ************************************************************************ *)

(** Introduce the head term, and return
    the new position to continue the proof. *)
let intro prefix pos =
  match Proof.apply_step pos Proof.intro prefix with
  | _, [| res |] -> res
  | _ -> assert false

let introN prefix n = iter (intro prefix) n

(** Cut *)
let cut ?(weak=false) ~f s t pos =
  match Proof.apply_step pos Proof.cut (not weak, s, t) with
  | id, [| aux ; main |] ->
    let () = f aux in
    id, main
  | _ -> assert false

(** Fixed arity applications *)
let applyN t n preludes pos =
  snd @@ Proof.apply_step pos Proof.apply (t, n, preludes)

let exact t preludes pos =
  match applyN t 0 preludes pos with
  | [| |] -> ()
  | _ -> assert false

let apply1 t preludes pos =
  match applyN t 1 preludes pos with
  | [| res |] -> res
  | _ -> assert false

let apply2 t preludes pos =
  match applyN t 2 preludes pos with
  | [| res1; res2 |] -> res1, res2
  | _ -> assert false

let apply3 t preludes pos =
  match applyN t 3 preludes pos with
  | [| res1; res2; res3 |] -> res1, res2, res3
  | _ -> assert false

let apply t preludes pos =
  let l, _ = Proof.match_arrows t.Term.ty in
  applyN t (List.length l) preludes pos

(* Splits for easy interaction with pipe operators *)
let split ~left ~right (p1, p2) =
  let () = left p1 in
  let () = right p2 in
  ()

let split3 ~first ~second ~third (p1, p2, p3) =
  let () = first p1 in
  let () = second p2 in
  let () = third p3 in
  ()

(** Apply exfalso if needed in order to get a goal of the form
    Gamma |- False *)
let exfalso pos =
  let ctx = extract_open pos in
  let g = Proof.goal ctx in
  try
    let _ = Term.pmatch ~pat:(Term.false_term) g in
    pos
  with Term.Match_Impossible _ ->
    apply1 (Term.app exfalso_term g) [] pos

(** Triviality: the goal is already present in the env *)
let trivial pos =
  let ctx = extract_open pos in
  let env = Proof.env ctx in
  let g = Proof.goal ctx in
  match Proof.Env.find env g with
  | id ->
    let () = exact (Term.id id) [] pos in
    true
  | exception Proof.Env.Not_introduced _ ->
    false

(** Find a contradiction in an environment using the given proposition. *)
let find_absurd seq env atom =
  match Proof.Env.find env atom with
  | p ->
    let neg_atom = Term.app Term.not_term atom in
    (* First, try and see wether [neg atom] is in the env *)
    begin match Proof.Env.find env neg_atom with
      | np -> (Term.app (Term.id np) (Term.id p))
      | exception Proof.Env.Not_introduced _ ->
        Util.debug ~section "@[<hv>Couldn't find in env (%d):@ %a@]"
          (Term.hash neg_atom) Term.print neg_atom;
        (* Try and see if [atom = neg q] with q in the context. *)
        begin try
            let q_v = Term.var "q" Term._Prop in
            let pat = Term.app Term.not_term (Term.id q_v) in
            let s = Term.pmatch ~pat atom in
            let q = Proof.Env.find env (Term.S.Id.get q_v s) in
            (Term.app (Term.id p) (Term.id q))
          with
          | Not_found ->
            Util.warn ~section "Internal error in pattern matching";
            assert false
          | Term.Match_Impossible _
          | Proof.Env.Not_introduced _ ->
            Util.warn ~section
              "@[<hv>Couldn't find an absurd situation using@ @[<hov>%a@]@ in env:@ %a@]"
              Term.print atom Proof.Env.print env;
            raise (Proof.Failure ("Logic.absurd", seq))
        end
    end
  | exception Proof.Env.Not_introduced _ ->
    Util.warn ~section
      "@[<hv>Trivial tactic failed because it couldn't find@ @[<hov>%a@]@ in env:@ %a@]"
      Term.print atom Proof.Env.print env;
    raise (Proof.Failure ("Logic.absurd", seq))

(** Given a goal of the form Gamma |- False,
    and a term, find its negation in the env, and close the branch *)
let absurd atom pos =
  let ctx = extract_open pos in
  let env = Proof.env ctx in
  pos |> exfalso |> exact (find_absurd ctx env atom) []


(* Logical connective elimination *)
(* ************************************************************************ *)

let or_left = Term.var "a" Term._Prop
let or_right = Term.var "b" Term._Prop
let or_elim_pat = Term.(apply or_term [id or_left; id or_right])

let rec or_elim ~f id pos =
  let ctx = extract_open pos in
  let goal = Proof.goal ctx in
  try
    let s = Term.pmatch ~pat:or_elim_pat id.Expr.id_type in
    let left_term = Term.S.Id.get or_left s in
    let right_term = Term.S.Id.get or_right s in
    let t' = Term.apply or_elim_term [left_term; right_term; goal; Term.id id] in
    apply2 t' [or_elim_alias] pos |> split
      ~left:(fun p -> p |> intro "O" |> find left_term (or_elim ~f))
      ~right:(fun p -> p |> intro "O" |> find right_term (or_elim ~f))
  with Term.Match_Impossible _ ->
    f id.Expr.id_type pos

let and_left = Term.var "a" Term._Prop
let and_right = Term.var "b" Term._Prop
let and_elim_pat = Term.(apply and_term [id or_left; id or_right])

let rec and_elim t pos =
  let ctx = extract_open pos in
  let goal = Proof.goal ctx in
  let env = Proof.env ctx in
  let v = Proof.Env.find env t in
  try
    let s = Term.pmatch ~pat:and_elim_pat v.Expr.id_type in
    let left_term = Term.S.Id.get and_left s in
    let right_term = Term.S.Id.get and_right s in
    let t' = Term.apply and_elim_term [left_term; right_term; goal; Term.id v] in
    apply1 t' [and_elim_alias] pos
    |> intro "A" |> intro "A"
    |> and_elim left_term
    |> and_elim right_term
  with Term.Match_Impossible _ -> pos


(* Resolution tactics *)
(* ************************************************************************ *)

let clause_type l =
  List.fold_right (fun lit acc ->
      Term.arrow (Term.app Term.not_term lit) acc
    ) l Term.false_term

let resolve_clause_aux c1 c2 res pos =
  let n = List.length res in
  pos
  |> iter (intro "L") n
  |> apply (Term.id c1) []
  |> Array.iter (fun p ->
      if not (trivial p) then begin
        p
        |> intro "x"
        |> apply (Term.id c2) []
        |> Array.iter (fun p' ->
            if not (trivial p') then begin
              let a = Proof.goal (extract_open p') in
              p' |> intro "y" |> absurd a
            end
          )
      end
    )

let resolve_clause c1 c2 res =
  let e = Proof.Env.empty in
  let e = Proof.Env.add e c1 in
  let e = Proof.Env.add e c2 in
  let goal = clause_type res in
  let p = Proof.mk (Proof.mk_sequent e goal) in
  let () = resolve_clause_aux c1 c2 res (Proof.pos @@ Proof.root p) in
  Proof.elaborate p

(* Classical tactics *)
(* ************************************************************************ *)

(** Apply NNPP if needed, in order to turn any sequent
    Gamma |- F, into a sequent of the form Gamma' |- False. *)
let nnpp pos =
  let ctx = extract_open pos in
  let goal = Proof.goal ctx in
  try
    (* If the goal is [ False], nothing to do *)
    let _ = Term.pmatch ~pat:Term.false_term goal in
    pos
  with Term.Match_Impossible _ ->
    begin try
        (* If the goal is a negation, directly use an intro,
           to stay intuitionistic as much as possible *)
        let p = Term.var "p" Term._Prop in
        let pat = Term.app Term.not_term @@ Term.id p in
        let _ = Term.pmatch ~pat goal in
        pos |> intro "G"
      with Term.Match_Impossible _ ->
        (* Else, apply NNPP, then intro to get the negation of the original goal
           as an hypothesis in the context *)
        pos
        |> apply1 (Term.app nnpp_term goal) [classical]
        |> intro "G"
    end


