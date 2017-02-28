
let section = Section.make ~parent:Dispatcher.section "logic"

module H = Hashtbl.Make(Expr.Formula)

let st = H.create 1024

let push name l = Dispatcher.push l (Dispatcher.mk_proof "logic" ~formula_args:l name)

let push_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    push "and" [Expr.Formula.neg r; Expr.Formula.f_false]
  else
    List.iter (fun p -> push "and" [Expr.Formula.neg r; p]) l

let push_or r l =
  if not (List.exists (Expr.Formula.equal Expr.Formula.f_true) l) then
    push "or" (Expr.Formula.neg r :: l)

let imply_left p = List.map Expr.Formula.neg @@
  match p with { Expr.formula = Expr.And l } -> l | p -> [p]

let imply_right = function { Expr.formula = Expr.Or l } -> l | q -> [q]

let tab = function
  (* 'True/False' traduction *)
  | { Expr.formula = Expr.False } ->
    raise (Dispatcher.Absurd ([Expr.Formula.f_true], (Dispatcher.mk_proof "logic" "true")))

  (* 'And' traduction *)
  | { Expr.formula = Expr.And l } as r ->
    push_and r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.And l } as r) } ->
    push_or (Expr.Formula.neg r) (List.rev_map Expr.Formula.neg l)

  (* 'Or' traduction *)
  | { Expr.formula = Expr.Or l } as r ->
    push_or r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Or l } as r) } ->
    push_and (Expr.Formula.neg r) (List.rev_map Expr.Formula.neg l)

  (* 'Imply' traduction *)
  | { Expr.formula = Expr.Imply (p, q) } as r ->
    let left = imply_left p in
    let right = imply_right q in
    push "imply" (Expr.Formula.neg r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply" [r; p];
    push "not-imply" [r; Expr.Formula.neg q]

  (* 'Equiv' traduction *)
  | { Expr.formula = Expr.Equiv (p, q) } as r ->
    push "equiv" [Expr.Formula.neg r; Expr.Formula.imply p q];
    push "equiv" [Expr.Formula.neg r; Expr.Formula.imply q p]
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equiv (p, q) } as r )  } ->
    push "not-equiv" [r; Expr.Formula.f_and [p; Expr.Formula.neg q]; Expr.Formula.f_and [Expr.Formula.neg p; q] ]

  (* Other formulas (not treated) *)
  | _ -> ()

let tab_assume f =
    if not (H.mem st f) then begin
      tab f;
      H.add st f true
    end

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose topconstructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~section ~assume:tab_assume ())

