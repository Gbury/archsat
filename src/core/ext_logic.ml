
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

  | Imply of Expr.formula
             * Expr.formula * Expr.formula list
             * Expr.formula * Expr.formula list

  | Not_imply_left of Expr.formula * Expr.formula
  | Not_imply_right of Expr.formula * Expr.formula

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

let imply_right = function
  | { Expr.formula = Expr.Or l } -> l
  | q -> [q]


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
    let left = imply_left p in
    let right = imply_right q in
    push "imply" (Imply (r, p, left, q, right)) (Expr.Formula.neg r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply_l" (Not_imply_left (r, p)) [r; p];
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
  | Imply (f, _, _, _, _)
  | Not_imply_left (f, _)
  | Not_imply_right (f, _)
  | Equiv_right (f, _)
  | Equiv_left (f, _)
  | Not_equiv (f, _, _) ->
    Some "LIGHTBLUE", [CCFormat.const Dot.Print.formula f]

let coq_imply_left_aux fmt (indent, (i, n)) =
  Util.debug ~section "coq_imply_left_aux (%d, (%d, %d))" indent n i;
  Format.fprintf fmt "%s %a. exact R."
    (String.make indent '+')
    Coq.Print.path (i, n)

let rec coq_imply_left fmt (total, n, i) =
  if n = 2 then
    Format.fprintf fmt "@[<v 2>%s destruct (%s _ _ T%d) as [R | R].@ %a@ %a@]"
      (if i = 0 then "-" else String.make i '+')
      "Coq.Logic.Classical_Prop.not_and_or" i
      coq_imply_left_aux (i + 1, (i + 1, total))
      coq_imply_left_aux (i + 1, (i + 2, total))
  else (* n > 2 *)
    Format.fprintf fmt "@[<v 2>%s destruct (%s _ _ T%d) as [R | T%d].@ %a@ %a@]"
      (if i = 0 then "-" else String.make i '+')
      "Coq.Logic.Classical_Prop.not_and_or" i (i + 1)
      coq_imply_left_aux (i + 1, (i + 1, total))
      coq_imply_left (total, n - 1, i + 1)

let rec coq_imply_right fmt (n, i) =
  if i > n then ()
  else begin
    Format.fprintf fmt "- %a. exact R.@ " Coq.Print.path (i, n);
    coq_imply_right fmt (n, i + 1)
  end

let coq_proof = function
  | True -> Coq.Raw (CCFormat.return "exact I.")

  | And (init, res) ->
    Coq.(Implication {
        left = [init];
        right = [res];
        prefix = "H";
        proof = (fun fmt m ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %a as %a; exact %s."
              (Proof.Ctx.named m) init
              (Print.pattern_and (fun fmt f ->
                   if Expr.Formula.equal f res
                   then Format.fprintf fmt "F"
                   else Format.fprintf fmt "_")) order
              "F"
          );
      })
  | Not_or (init, res) ->
    Coq.(Implication {
        left = [res];
        right = [init];
        prefix = "H";
        proof = (fun fmt m ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "%a.@ exact %a."
              Print.path_to (res, order) (Proof.Ctx.named m) res
          )
      })

  | Or (init, l) ->
    Coq.(Implication {
        left = [init];
        right = l;
        prefix = "H";
        proof = (fun fmt m ->
            let n = List.length l in
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %a as %a.@\n@[<hv>%a@]"
              (Proof.Ctx.named m) init
              (Print.pattern_or (fun fmt f -> Format.fprintf fmt "F")) order
            (fun fmt -> List.iteri (fun i _ ->
                  Format.fprintf fmt "@[<hov 2>- %a.@ exact F.@]@ "
                    Print.path (i + 1, n))) l
          )
      })
  | Not_and (init, l) ->
    Coq.(Implication {
        left = l;
        right = [init];
        prefix = "H";
        proof = (fun fmt m ->
            let aux = Proof.Ctx.named m in
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "exact @[<hov>%a@]." (Print.pattern_intro_and aux) order
          )
      })

  | Imply (init, _, [p], _, [q]) ->
    Coq.(Ordered {
        order = [Expr.Formula.neg init; p; q];
        proof = (fun fmt () ->
            Format.fprintf fmt "apply Coq.Logic.Classical_Prop.imply_to_or.@ ";
            Format.fprintf fmt "apply Coq.Logic.Classical_Prop.imply_to_or."
          );
      })
  | Imply (init, p, lp, q, lq) ->
    Coq.(Implication {
        left = [init];
        right = lp @ lq;
        prefix = "H";
        proof = (fun fmt m ->
            let np = List.length lp in
            let nq = List.length lq in
            let order_right = CCOpt.get_exn (Expr.Formula.get_tag q Expr.f_order) in
            Format.fprintf fmt
              "destruct (Coq.Logic.Classical_Prop.imply_to_or _ _ %a) as [T0 | %a].@\n"
              (Proof.Ctx.named m) init
              (Print.pattern_or (fun fmt _ -> Format.fprintf fmt "R")) order_right;
            Format.fprintf fmt "@[<v>%a@ %a@]"
              coq_imply_left (np + nq, np, 0) coq_imply_right (np + nq, np + 1)
          )
      })

  | Not_imply_left (init, res) ->
    Coq.(Ordered {
        order = [res; init];
        proof = (fun fmt () ->
            Format.fprintf fmt "apply Coq.Logic.Classical_Prop.NNPP. intro H0.@ ";
            Format.fprintf fmt
              "destruct (Coq.Logic.Classical_Prop.not_or_and _ _ H0) as [H1 H2].@ ";
            Format.fprintf fmt "exact (H1 (Coq.Logic.Classical_Prop.not_imply_elim _ _ H2))."
          )
      })
  | Not_imply_right (init, res) ->
    Coq.(Implication {
        left = [res];
        right = [init];
        prefix = "H";
        proof = (fun fmt m ->
            Format.fprintf fmt "intros _; exact %a." (Proof.Ctx.named m) res
          )
      })

  | Equiv_right (init, res) ->
    Coq.(Implication {
        left = [init];
        right = [res];
        prefix = "E";
        proof = (fun fmt m ->
            Format.fprintf fmt "destruct (iff_and %a) as [R _]; exact R."
              (Proof.Ctx.named m) init
          )
      })
  | Equiv_left (init, res) ->
    Coq.(Implication {
        left = [init];
        right = [res];
        prefix = "E";
        proof = (fun fmt m ->
            Format.fprintf fmt "destruct (iff_and %a) as [_ R]; exact R."
              (Proof.Ctx.named m) init
          )
      })

  | Not_equiv (init, pq, qp) ->
    Coq.(Implication {
        left = [pq; qp];
        right = [init];
        prefix = "I";
        proof = (fun fmt m ->
            Format.fprintf fmt "rewrite iff_to_and. split; assumption."
          )
      })

(* Handle & plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Logic info -> Some (dot_info info)
  | Coq.Prove Logic info -> Some(coq_proof info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose top constructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~assume:tab_assume ())

