
let log_section = Util.Section.make "eq"
let log i fmt = Util.debug ~section:log_section i fmt

module D = Dispatcher
module E = Eclosure.Make(Expr.Term)

let st = E.create D.stack

let name = "eq"
let watch = D.watch name

let eq_eval f = match f with
  | { Expr.formula = Expr.Equal (a, b) } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        log 30 "Eval [%a] %a (%d) == %a (%d)" Expr.Debug.formula f Expr.Debug.term a' lvl_a Expr.Debug.term b' lvl_b;
        Some (Expr.Term.equal a' b', max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        log 30 "Eval [%a] %a (%d) <> %a (%d)" Expr.Debug.formula f Expr.Debug.term a' lvl_a Expr.Debug.term b' lvl_b;
        Some (not (Expr.Term.equal a' b'), max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

let f_eval f () =
  match eq_eval f with
  | Some(true, lvl) -> D.propagate f lvl
  | Some(false, lvl) -> D.propagate (Expr.Formula.neg f) lvl
  | None -> ()

let mk_expl (a, b, l) =
  let rec aux acc = function
    | [] | [_] -> acc
    | x :: ((y :: _) as r) ->
      aux (Expr.Formula.eq x y :: acc) r
  in
  (Expr.Formula.eq a b) :: (List.rev_map Expr.Formula.neg (aux [] l))

let mk_proof l =
  assert (l <> []);
  Dispatcher.mk_proof name ~term_args:l "eq-trans"

let wrap f x y =
  try
    f st x y
  with E.Unsat (a, b, l) ->
    log 2 "Error while adding hypothesis : %a ~ %a" Expr.Debug.term x Expr.Debug.term y;
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let tag x () =
  try
    log 10 "Tagging %a" Expr.Debug.term x;
    E.add_tag st x (fst (D.get_assign x))
  with E.Unsat (a, b, l) ->
    log 2 "Error while tagging : %a -> %a" Expr.Debug.term x Expr.Debug.term (fst (D.get_assign x));
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let eq_assign x =
  try
    begin match E.find_tag st x with
      | _, Some (_, v) -> log 5 "Found tag : %a" Expr.Debug.term v; v
      | x, None ->
        log 5 "Looking up repr : %a" Expr.Debug.term x;
        try fst (D.get_assign x) with D.Not_assigned _ -> x
    end
  with E.Unsat (a, b, l) ->
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let eq_assume (f, _) = match f with
  | { Expr.formula = Expr.Equal (a, b)} ->
    wrap E.add_eq a b;
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b)} } ->
    wrap E.add_neq a b;
  | _ -> ()

let rec set_handler t =
  let aux v =
    if not Expr.(Ty.equal v.id_type Ty.prop) then
      Expr.Id.set_assign v 0 eq_assign
  in
  watch 1 [t] (tag t);
  match t with
  | { Expr.term = Expr.Var v } -> aux v
  | { Expr.term = Expr.Meta m } -> aux Expr.(m.meta_id)
  | { Expr.term = Expr.App (f, _, l) } ->
    if not Expr.(Ty.equal f.id_type.fun_ret Ty.prop) then
      Expr.Id.set_assign f 0 eq_assign;
    List.iter set_handler l

let eq_pre = function
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    watch 1 [a; b] (f_eval f);
    set_handler a;
    set_handler b
  | { Expr.formula = Expr.Pred p } ->
    set_handler p
  | _ -> ()

;;
D.Plugin.register name
  ~descr:"Ensures consistency of assignment with regards to the equality predicates."
  (D.mk_ext
     ~assume:eq_assume
     ~eval_pred:eq_eval
     ~peek:eq_pre
     ()
  )
