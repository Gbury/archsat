
let log_section = Util.Section.make "eq"
let log i fmt = Util.debug ~section:log_section i fmt

module D = Dispatcher
module E = Ec.Make(Expr.Term)

let st = E.create D.stack

let id = D.new_id ()
let watch = D.watch id

let eq_eval f = match f with
  | { Expr.formula = Expr.Equal (a, b) } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        log 30 "Eval [%a] %a (%d) == %a (%d)" Expr.debug_formula f Expr.debug_term a' lvl_a Expr.debug_term b' lvl_b;
        Some (Expr.Term.equal a' b', max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        log 30 "Eval [%a] %a (%d) <> %a (%d)" Expr.debug_formula f Expr.debug_term a' lvl_a Expr.debug_term b' lvl_b;
        Some (not (Expr.Term.equal a' b'), max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

let f_eval f () =
  match eq_eval f with
  | Some(true, lvl) -> D.propagate f lvl
  | Some(false, lvl) -> D.propagate (Expr.f_not f) lvl
  | None -> ()

let mk_expl (a, b, l) =
  let rec aux acc = function
    | [] | [_] -> acc
    | x :: ((y :: _) as r) ->
      aux (Expr.f_equal x y :: acc) r
  in
  (Expr.f_equal a b) :: (List.rev_map Expr.f_not (aux [] l))

let mk_proof l =
  assert (l <> []);
  Dispatcher.mk_proof ~term_args:l id "eq-trans"

let wrap f x y =
  try
    f st x y
  with E.Unsat (a, b, l) ->
    log 2 "Error while adding hypothesis : %a ~ %a" Expr.debug_term x Expr.debug_term y;
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let tag x () =
  try
    log 10 "Tagging %a" Expr.debug_term x;
    E.add_tag st x (fst (D.get_assign x))
  with E.Unsat (a, b, l) ->
    log 2 "Error while tagging : %a -> %a" Expr.debug_term x Expr.debug_term (fst (D.get_assign x));
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let eq_assign x =
  try
    begin match E.find_tag st x with
      | _, Some (_, v) -> log 5 "Found tag : %a" Expr.debug_term v; v
      | x, None ->
        log 5 "Looking up repr : %a" Expr.debug_term x;
        try fst (D.get_assign x) with D.Not_assigned _ -> x
    end
  with E.Unsat (a, b, l) ->
    log 0 "WUUUT ?!!";
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let eq_assume (f, _) = match f with
  | { Expr.formula = Expr.Equal (a, b)} ->
    wrap E.add_eq a b;
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b)} } ->
    wrap E.add_neq a b;
  | _ -> ()

let rec set_handler t =
  let aux v =
    if not Expr.(Ty.equal v.var_type type_prop) then
      Expr.set_assign v 0 eq_assign
  in
  watch 1 [t] (tag t);
  match t with
  | { Expr.term = Expr.Var v } -> aux v
  | { Expr.term = Expr.Meta m } -> aux Expr.(m.meta_var)
  | { Expr.term = Expr.App (f, _, l) } ->
    if not Expr.(Ty.equal f.var_type.fun_ret type_prop) then
      Expr.set_assign f 0 eq_assign;
    List.iter set_handler l

let rec eq_pre = function
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    watch 1 [a; b] (f_eval f);
    set_handler a;
    set_handler b
  | { Expr.formula = Expr.Pred p } ->
    set_handler p
  | { Expr.formula = Expr.Not f } ->
    eq_pre f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter eq_pre l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    eq_pre p;
    eq_pre q
  | { Expr.formula = Expr.All (_, _, f) }
  | { Expr.formula = Expr.AllTy (_, _, f) }
  | { Expr.formula = Expr.Ex (_, _, f) }
  | { Expr.formula = Expr.ExTy (_, _, f) } ->
    eq_pre f
  | _ -> ()

;;
D.(register (
    mk_ext
      ~descr:"Ensures consistency of assignment with regards to the equality predicates."
      ~assume:eq_assume
      ~eval_pred:eq_eval
      ~peek:eq_pre
      id "eq"
  ))
