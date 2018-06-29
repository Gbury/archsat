
let section = Section.make ~parent:Dispatcher.section "logic"

(* Module aliases & initialization *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Formula)

type info =
  | True

  | And of Expr.formula * Expr.formula
  | Not_or of Expr.formula * Expr.formula

  | Or of Expr.formula * Expr.formula list
  | Not_and of Expr.formula * Expr.formula list

  | Imply_chain of Expr.formula *
                   Expr.formula list *
                   Expr.formula list *
                   Expr.formula * Expr.formula list

  | Not_imply_right of Expr.formula * Expr.formula
  | Not_imply_left of Expr.formula * Expr.formula * Expr.formula

  | Equiv_right of Expr.formula * Expr.formula
  | Equiv_left of Expr.formula * Expr.formula

  | Not_equiv of Expr.formula * Expr.formula * Expr.formula

type Dispatcher.lemma_info += Logic of info

let st = H.create 1024

(* Small wrappers *)
(* ************************************************************************ *)

let push name info l =
  Dispatcher.push l (Dispatcher.mk_proof "logic" name (Logic info))

let push_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    push "and" (And (r, Expr.Formula.f_false))
      [Expr.Formula.neg r; Expr.Formula.f_false]
  else
    List.iter (fun p -> push "and" (And (r, p)) [Expr.Formula.neg r; p]) l

let push_not_or r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) l then
    push "not-or" (Not_or (r, Expr.Formula.f_false))
      [ r; Expr.Formula.f_false ]
  else
    List.iter (fun p -> push "not-or" (Not_or (r, p)) [r; Expr.Formula.neg p]) l

let push_or r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) l then
    () (* clause is trivially true *)
  else
    push "or" (Or (r, l)) (Expr.Formula.neg r :: l)

let push_not_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    () (* clause is trivially true *)
  else
    push "not-and" (Not_and (r, l)) (r :: List.rev_map Expr.Formula.neg l)

let imply_left p =
  List.map Expr.Formula.neg @@
  match p with
  | { Expr.formula = Expr.And l } -> l
  | p -> [p]

let pattern_imply_left = function
  | { Expr.formula = Expr.And _ } as p ->
    CCOpt.get_exn @@ Expr.Formula.get_tag p Expr.f_order
  | p -> Expr.(L [F p])

let imply_right = function
  | { Expr.formula = Expr.Or l } -> l
  | q -> [q]

let rec imply_chain acc left = function
  | { Expr.formula = Expr.Imply (p, q) } ->
    imply_chain (p :: acc) ((imply_left p) @ left) q
  | f -> (List.rev acc), left, f, imply_right f

(* Main function *)
(* ************************************************************************ *)

let tab = function
  (* 'True/False' traduction *)
  | { Expr.formula = Expr.False } ->
    raise (Dispatcher.Absurd
             ([Expr.Formula.f_true],
              Dispatcher.mk_proof "logic" "true" (Logic True)))

  (* 'And' traduction *)
  | { Expr.formula = Expr.And l } as r ->
    push_and r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.And l } as r) } ->
    push_not_and r l

  (* 'Or' traduction *)
  | { Expr.formula = Expr.Or l } as r ->
    push_or r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Or l } as r) } ->
    push_not_or r l

  (* 'Imply' traduction *)
  | { Expr.formula = Expr.Imply (p, q) } as r ->
    let l, left, s, right = imply_chain [] [] r in
    push "imply" (Imply_chain (r, l, left, s, right)) (Expr.Formula.neg r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply_l" (Not_imply_left (r, p, q)) [r; p];
    push "not-imply_r" (Not_imply_right (r, q)) [r; Expr.Formula.neg q]

  (* 'Equiv' traduction *)
  | { Expr.formula = Expr.Equiv (p, q) } as r ->
    let nr = Expr.Formula.neg r in
    let pq = Expr.Formula.imply p q in
    let qp = Expr.Formula.imply q p in
    push "equiv_r" (Equiv_right (r, pq)) [nr; pq];
    push "equiv_l" (Equiv_left (r, qp)) [nr; qp]
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equiv (p, q) } as r )  } ->
    let pq = Expr.Formula.imply p q in
    let qp = Expr.Formula.imply q p in
    push "not-equiv" (Not_equiv (r, pq, qp))
      [ r; Expr.Formula.neg pq; Expr.Formula.neg qp ]

  (* Other formulas (not treated) *)
  | _ -> ()

let tab_assume f =
    if not (H.mem st f) then begin
      tab f;
      H.add st f true
    end

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | True -> None, []

  | And (t, t') ->
    Some "LIGHTBLUE", List.map (CCFormat.const Dot.Print.formula) [t; t']
  | Not_or (t, t') ->
    Some "LIGHTBLUE", List.map (CCFormat.const Dot.Print.formula) [t; t']

  | Or (f, _)
  | Not_and (f, _)
  | Imply_chain (f, _, _, _, _)
  | Not_imply_left (f, _, _)
  | Not_imply_right (f, _)
  | Equiv_right (f, _)
  | Equiv_left (f, _)
  | Not_equiv (f, _, _) ->
    Some "LIGHTBLUE", [CCFormat.const Dot.Print.formula f]

let coq_proof = function
  | True -> (* prove: ~ True -> False *)
    (fun p -> p
              |> Logic.intro "Ax"
              |> Logic.ctx (fun seq ->
                  Logic.exact [] (
                    let not_true = Proof.Env.find (Proof.env seq)
                        (Term.app Term.not_term Term.true_term) in
                    Term.app (Term.id not_true) Logic.true_proof)
                )
    )
  | And (init, res) -> (* prove: ~ ~ init -> ~ res -> False,
                          with init a conjunction including res *)
    (fun p -> p
              |> Logic.introN "Ax" 2
              |> Logic.not_not_elim "Ax" (Term.of_formula init)
              |> Logic.find (Term.of_formula init) Logic.and_elim
              |> Logic.absurd (Term.of_formula res))

  | Not_or (init, res) -> (* prove ~ init -> ~ ~ res -> False,
                             with init a disjunction that includes res *)
    (fun p -> p
              |> Logic.introN "Ax" 2
              |> Logic.normalize "Ax" (Term.of_formula res)
              |> Logic.find
                (Term.app Term.not_term (Term.of_formula init)) (Logic.apply1 [])
              |> Logic.or_intro (Term.of_formula res)
              |> Logic.ensure Logic.trivial)

  | Or (init, l) -> (* prove ~ ~ init -> ~ l_1 -> .. -> ~ l_n -> False
                       with init a disjunction [ \/ l_i ] and [ l = l_1; l_2, ...] *)
    (fun p -> p
              |> Logic.introN "Ax" (1 + List.length l)
              |> Logic.not_not_elim "Ax" (Term.of_formula init)
              |> Logic.find (Term.of_formula init) (Logic.or_elim ~f:Logic.absurd)
    )

  | Not_and (init, l) -> (* prove ~init -> ~ ~ l_1 -> .. -> ~ ~ l_n -> False
                            with init a conjunction [/\ l_i] and [l = l_1;l_2...] *)
    (fun p -> p
              |> Logic.introN "Ax" (1 + List.length l)
              |> Logic.fold (Logic.normalize "Ax") (List.map Term.of_formula l)
              |> Logic.find (Term.of_formula (Expr.Formula.neg init)) (Logic.apply1 [])
              |> Logic.and_intro ~f:(fun _ -> Logic.ensure Logic.trivial)
    )

  | Equiv_left (init, res)
  | Equiv_right (init, res) -> (* prove ~ ~ init -> ~ res -> False,
                                  with init a equivalence [p <-> q],
                                  and res an implication [p -> q] or [q -> p] *)
    (fun p -> p
              |> Logic.introN "Ax" 2
              |> Logic.not_not_elim "Ax" (Term.of_formula init)
              |> Logic.find (Term.of_formula init) Logic.and_elim
              |> Logic.absurd (Term.of_formula res))

  | Not_equiv (init, pq, qp) -> (* prove ~ init -> ~ ~ pq -> ~ ~ qp -> False
                                   with init an equivalence [p <-> q],
                                        pq an implication [p -> q],
                                        qp an implication [q -> p] *)
    (fun p -> p
              |> Logic.introN "Ax" 3
              |> Logic.not_not_elim "Ax" (Term.of_formula pq)
              |> Logic.not_not_elim "Ax" (Term.of_formula qp)
              |> Logic.find (Term.of_formula (Expr.Formula.neg init)) @@ Logic.apply1 []
              |> Logic.and_intro ~f:(fun _ -> Logic.ensure Logic.trivial)
    )

  | Imply_chain (init, left, l, right, l') -> (** prove
                                          ~ ~ init ->
                                          {~ ~ x}_{x in l} ->
                                          {~ y}_{y in l'} -> False,
                                          where init is an implication
                                          [l_1 -> (l_2 /\ l_3) -> ... -> q]
                                          and right a disjunction of formulas in l'. *)
    (fun p ->
       Util.debug ~section "Proving translation for@ %a" Expr.Formula.print init;
       p
       |> Logic.introN "Ax" (1 + List.length l + List.length l')
       |> Logic.not_not_elim "Ax" (Term.of_formula init)
       |> Logic.fold (Logic.normalize "Ax") (
         List.map (fun f -> Term.of_formula @@ Expr.Formula.neg f) l)
       |> Logic.ctx (fun seq ->
           Util.debug ~section "Building implication";
           let env = Proof.env seq in
           let imply = Proof.Env.find env (Term.of_formula init) in
           let args = List.map (fun x ->
               Util.debug ~section "And-intro for@ %a" Expr.Formula.print x;
               let t = Term.of_formula x in
               let p = Proof.mk (Proof.mk_sequent env t) in
               let pos = Proof.pos @@ Proof.root p in
               let () = Logic.and_intro ~f:(fun _ -> Logic.(ensure trivial)) pos in
               Proof.elaborate p
             ) left in
           Logic.or_elim ~f:Logic.absurd (Term.apply (Term.id imply) args)
         )
    )

  | Not_imply_left (init, p, q) -> (* prove ~ init -> ~ p -> False
                                      with init an implication [p -> q] *)
    (fun pos -> pos
              |> Logic.introN "Ax" 2
              |> Logic.find (Term.of_formula @@ Expr.Formula.neg init) (Logic.apply1 [])
              |> Logic.intro "I"
              |> Logic.absurd (Term.of_formula p)
    )

  | Not_imply_right (init, q) -> (* prove ~ init -> ~ ~ q -> False
                                    with init an implication [p -> q] *)
    (fun pos -> pos
                |> Logic.introN "Ax" 2
                |> Logic.normalize "Ax" (Term.of_formula q)
                |> Logic.find (Term.of_formula @@ Expr.Formula.neg init) (Logic.apply1 [])
                |> Logic.intro "I"
                |> Logic.ensure Logic.trivial
    )


(* Handle & plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Logic info -> Some (dot_info info)
  | Proof.Lemma Logic info -> Some (coq_proof info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose top constructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~assume:tab_assume ())

