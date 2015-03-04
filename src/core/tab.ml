
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()
let st = H.create 1024

let push name l = Dispatcher.push l (Dispatcher.mk_proof ~formula_args:l id ("tab-" ^ name))

let push_and r l =
  if List.exists (Expr.Formula.equal Expr.f_false) l then
    push "and" [Expr.f_not r; Expr.f_false]
  else
    List.iter (fun p -> push "and" [Expr.f_not r; p]) l

let push_or r l =
  if not (List.exists (Expr.Formula.equal Expr.f_true) l) then
    push "or" (Expr.f_not r :: l)

let tab = function
  (* 'True/False' traduction *)
  | { Expr.formula = Expr.False } ->
    raise (Dispatcher.Absurd ([Expr.f_true], (Dispatcher.mk_proof id "true")))

  (* 'And' traduction *)
  | { Expr.formula = Expr.And l } as r ->
    push_and r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.And l } as r) } ->
    push_or (Expr.f_not r) (List.rev_map Expr.f_not l)

  (* 'Or' traduction *)
  | { Expr.formula = Expr.Or l } as r ->
    push_or r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Or l } as r) } ->
    push_and (Expr.f_not r) (List.rev_map Expr.f_not l)

  (* 'Imply' traduction *)
  | { Expr.formula = Expr.Imply (p, q) } as r ->
    let left = List.map Expr.f_not (match p with
      | { Expr.formula = Expr.And l } -> l
      | _ -> [p]) in
    let right = match q with
      | { Expr.formula = Expr.Or l } -> l
      | _ -> [q] in
    push "imply" (Expr.f_not r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply" [r; p];
    push "not-imply" [r; Expr.f_not q]

  (* 'Equiv' traduction *)
  | { Expr.formula = Expr.Equiv (p, q) } as r ->
    push "equiv" [Expr.f_not r; Expr.f_not p; q];
    push "equiv" [Expr.f_not r; Expr.f_not q; p]
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equiv (p, q) } as r )  } ->
    push "not-equiv" [r; Expr.f_and [p; Expr.f_not q]; Expr.f_and [Expr.f_not p; q] ]

  (* Other formulas (not treated) *)
  | _ -> ()

let tab_assume (f, i) =
  try
      ignore (H.find st f)
  with Not_found ->
      tab f;
      H.add st f i

let tab_eval _ = None

let tab_pre _ = ()

;;
Dispatcher.(register {
    id = id;
    name = "tab";
    assume = tab_assume;
    eval_pred = tab_eval;
    preprocess = tab_pre;
    if_sat = (fun _ -> ());
    options = (function t -> t);
  })

