
let section = Section.make ~parent:Proof.section "logic"

(* Logic preludes *)
(* ************************************************************************ *)

(* TODO: dispatch system for language-specific printing *)
let classical =
  Proof.Prelude.require (Expr.Id.mk_new "classical" ())
(* -> Coq.Logic.Classical *)

(* Useful constants *)
(* ************************************************************************ *)

let exfalso_id =
  let p = Term.declare "P" Term._Prop in
  Term.declare "exfalso" (Term.forall p (
      Term.arrow Term.false_term (Term.const p)))

let nnpp_id =
  let p = Term.declare "P" Term._Prop in
  let p_t = Term.const p in
  let nnp = Term.app Term.not_term (Term.app Term.not_term p_t) in
  Term.declare "NNPP" (Term.forall p (Term.arrow nnp p_t))

let nnpp_term = Term.const nnpp_id
let exfalso_term = Term.const exfalso_id

(* Some generic tactic manipulations *)
(* ************************************************************************ *)

let extract_open pos =
  match Proof.extract @@ Proof.get pos with
  | Proof.Open sequent -> sequent
  | Proof.Proof _ -> assert false

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
    let () = exact (Term.const id) [] pos in
    true
  | exception Proof.Env.Not_introduced _ ->
    false

(** Find a contradiction in an environment using the given proposition. *)
let find_absurd env atom =
  match Proof.Env.find env atom with
  | p ->
    (* First, try and see wether [neg atom] is in the env *)
    begin match Proof.Env.find env (Term.app Term.not_term atom) with
      | np -> (Term.app (Term.const np) (Term.const p))
      | exception Proof.Env.Not_introduced _ ->
        (* Try and see if [atom = neg q] with q in the context. *)
        begin try
            let q_v = Term.declare "q" Term._Prop in
            let pat = Term.app Term.not_term (Term.const q_v) in
            let s = Term.pmatch ~pat atom in
            let q = Proof.Env.find env (Term.S.Id.get q_v s) in
            (Term.app (Term.const p) (Term.const q))
          with
          | Not_found ->
            Util.warn ~section "Internal error in pattern matching";
            assert false
          | Term.Match_Impossible _
          | Proof.Env.Not_introduced _ ->
            Util.warn ~section
              "Couldn't find an absurd situation in env:@ %a" Proof.Env.print env;
            assert false
        end
    end
  | exception Proof.Env.Not_introduced _ ->
    Util.warn ~section
      "Trivial tactic failed because it couldn't find@ %a in env:@ %a"
      Term.print atom Proof.Env.print env;
    assert false

(** Given a goal of the form Gamma |- False,
    and a term, find its negation in the env, and close the branch *)
let absurd atom pos =
  let ctx = extract_open pos in
  let env = Proof.env ctx in
  pos |> exfalso |> exact (find_absurd env atom) []

(* Resolution tactics *)
(* ************************************************************************ *)

let resolve_clause_aux c1 c2 res pos =
  let n = List.length res in
  pos
  |> iter (intro "L") n
  |> apply (Term.const c1) []
  |> Array.iter (fun p ->
      if not (trivial p) then begin
        p
        |> intro "x"
        |> apply (Term.const c2) []
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
  let goal = List.fold_right (fun l c ->
      Term.arrow (Term.app Term.not_term l) c) res Term.false_term in
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
        let p = Term.declare "p" Term._Prop in
        let pat = Term.app Term.not_term @@ Term.const p in
        let _ = Term.pmatch ~pat goal in
        pos |> intro "G"
      with Term.Match_Impossible _ ->
        (* Else, apply NNPP, then intro to get the negation of the original goal
           as an hypothesis in the context *)
        pos
        |> apply1 (Term.app nnpp_term goal) [classical]
        |> intro "G"
    end


