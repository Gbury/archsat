
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
                   Expr.formula

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
    push "imply" (Imply_chain (r, l, left, s)) (Expr.Formula.neg r :: (left @ right))
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
  | Imply_chain (f, _, _, _)
  | Not_imply_left (f, _, _)
  | Not_imply_right (f, _)
  | Equiv_right (f, _)
  | Equiv_left (f, _)
  | Not_equiv (f, _, _) ->
    Some "LIGHTBLUE", [CCFormat.const Dot.Print.formula f]

let coq_proof = function
  | True ->
    Coq.tactic ~prefix:"X" (fun fmt ctx ->
            Coq.exact fmt "%a I" (Proof.Ctx.named ctx) (Expr.Formula.f_false)
          )

  | And (init, res) ->
    Coq.tactic ~prefix:"A" ~normalize:Coq.All (fun fmt ctx ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %a as %a.@ exact F."
              (Proof.Ctx.named ctx) init
              (Coq.Print.pattern_and (fun fmt f ->
                   if Expr.Formula.equal f res
                   then Format.fprintf fmt "F"
                   else Format.fprintf fmt "_")) order
          )
  | Not_or (init, res) ->
    Coq.tactic ~prefix:"O" ~normalize:Coq.All (fun fmt ctx ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "apply %a.@ %a. exact %a."
              (Proof.Ctx.named ctx) (Expr.Formula.neg init)
              Coq.Print.path_to (res, order) (Proof.Ctx.named ctx) res
          )

  | Or (init, l) ->
    Coq.tactic ~prefix:"O" ~normalize:(Coq.Mem [init]) (fun fmt ctx ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %a as %a.@ @[<hv>%a@]"
              (Proof.Ctx.named ctx) init
              (Coq.Print.pattern_or (fun fmt f -> Format.fprintf fmt "F")) order
              CCFormat.(list ~sep:(return "@ ") (fun fmt f ->
                  Format.fprintf fmt "exact (%a F)."
                    (Proof.Ctx.named ctx) (Expr.Formula.neg f)
                )) l
          )
  | Not_and (init, l) ->
    Coq.tactic ~prefix:"A" ~normalize:Coq.All (fun fmt ctx ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "exact (%a @[<hov>%a@])."
              (Proof.Ctx.named ctx) (Expr.Formula.neg init)
              (Coq.Print.pattern_intro_and (Proof.Ctx.named ctx)) order
          )
  | Imply_chain (init, left, l, q) ->
    Coq.tactic ~prefix:"Ax"
      ~normalize:(Coq.Mem (init :: (List.map Expr.Formula.neg l))) (fun fmt ctx ->
        Format.fprintf fmt "specialize (%a @[<hov>%a@]).@ "
          (Proof.Ctx.named ctx) init
          CCFormat.(list ~sep:(return "@ ") (fun fmt f ->
              Coq.Print.pattern_intro_and (Proof.Ctx.named ctx) fmt
                (pattern_imply_left f)
            )) left;
        match Expr.Formula.get_tag q Expr.f_order with
        | None ->
          Coq.exact fmt "%a %a"
            (Proof.Ctx.named ctx) (Expr.Formula.neg q)
            (Proof.Ctx.named ctx) init
        | Some o ->
          Format.fprintf fmt "destruct %a as @[<hov>%a@].@ "
            (Proof.Ctx.named ctx) init
            (Coq.Print.pattern_or (Proof.Ctx.named ctx)) o;
          Coq.Print.pattern ~start:CCFormat.silent ~stop:CCFormat.silent
            ~sep:(CCFormat.return "@ ") (fun fmt f ->
                Coq.exact fmt "%a %a"
                  (Proof.Ctx.named ctx) (Expr.Formula.neg f)
                  (Proof.Ctx.named ctx) f
              ) fmt o
        )

  | Not_imply_left (init, p, q) ->
    Coq.tactic ~prefix:"Ax" ~normalize:(Coq.Mem []) (fun fmt ctx ->
        Coq.exact fmt "%a (fun %a => False_ind %a (%a %a))"
          (Proof.Ctx.named ctx) (Expr.Formula.neg init)
          (Proof.Ctx.intro ctx) p
          Coq.Print.formula q
          (Proof.Ctx.named ctx) (Expr.Formula.neg p)
          (Proof.Ctx.named ctx) p
      )
  | Not_imply_right (init, res) ->
    Coq.tactic ~prefix:"Ax" (fun fmt ctx ->
        Coq.exact fmt "%a (fun _ => %a)"
          (Proof.Ctx.named ctx) (Expr.Formula.neg init)
          (Proof.Ctx.named ctx) res
      )

  | Equiv_right (init, res)
  | Equiv_left (init, res) ->
    Coq.tactic ~prefix:"E" (fun fmt ctx ->
        Format.fprintf fmt "apply %a.@ rewrite %a.@ exact (fun x => x)."
          (Proof.Ctx.named ctx) (Expr.Formula.neg res)
          (Proof.Ctx.named ctx) init
      )

  | Not_equiv (init, pq, qp) ->
    Coq.tactic ~prefix:"I" (fun fmt ctx ->
        Format.fprintf fmt "apply %a.@ split.@ exact (%a).@ exact (%a)."
          (Proof.Ctx.named ctx) (Expr.Formula.neg init)
          (Proof.Ctx.named ctx) pq
          (Proof.Ctx.named ctx) qp
      )

(* Handle & plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Logic info -> Some (dot_info info)
  | Coq.Tactic Logic info -> Some (coq_proof info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose top constructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~assume:tab_assume ())

