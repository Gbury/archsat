
let section = Section.make ~parent:Dispatcher.section "logic"

(* Module aliases & initialization *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Formula)

type info =
  | True
  | And_false
  | And of Expr.formula * Expr.formula
  | Or of Expr.formula
  | Imply of Expr.formula
  | Not_imply_left of Expr.formula
  | Not_imply_right of Expr.formula
  | Equiv_right of Expr.formula
  | Equiv_left of Expr.formula
  | Not_equiv of Expr.formula

type Dispatcher.lemma_info += Logic of info

let st = H.create 1024

(* Small wrappers *)
(* ************************************************************************ *)

let push name info l =
  Dispatcher.push l (Dispatcher.mk_proof "logic" name (Logic info))

let push_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    push "and" And_false [Expr.Formula.neg r; Expr.Formula.f_false]
  else
    List.iter (fun p -> push "and" (And (r, p)) [Expr.Formula.neg r; p]) l

let push_or r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) l then
    () (* clause is trivially true *)
  else
    push "or" (Or r) (Expr.Formula.neg r :: l)

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
    push "imply" (Imply r) (Expr.Formula.neg r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply_l" (Not_imply_left r) [r; p];
    push "not-imply_r" (Not_imply_right r) [r; Expr.Formula.neg q]

  (* 'Equiv' traduction *)
  | { Expr.formula = Expr.Equiv (p, q) } as r ->
    push "equiv" (Equiv_right r) [Expr.Formula.neg r; Expr.Formula.imply p q];
    push "equiv" (Equiv_left r) [Expr.Formula.neg r; Expr.Formula.imply q p]
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equiv (p, q) } as r )  } ->
    push "not-equiv" (Not_equiv r)
      [r; Expr.Formula.f_and [p; Expr.Formula.neg q]; Expr.Formula.f_and [Expr.Formula.neg p; q] ]

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
  | And_false -> None, []
  | And (t, t') ->
    None, List.map (CCFormat.const Expr.Print.formula) [t; t']
  | Or f
  | Imply f
  | Not_imply_left f
  | Not_imply_right f
  | Equiv_right f
  | Equiv_left f
  | Not_equiv f ->
    None, [CCFormat.const Expr.Print.formula f]

(* Handle & plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Logic info -> Some (dot_info info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose topconstructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~assume:tab_assume ())

