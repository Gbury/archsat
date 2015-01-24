
module D = Dispatcher
module E = Ec.Make(Expr.Term)

let st = E.create D.stack

let eq_eval = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        Some (Expr.Term.equal a' b', max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
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

let wrap f x y =
    try
        f st x y
    with E.Unsat (a, b, l) ->
        raise (D.Absurd (mk_expl (a, b, l)))

let tag x () =
    try
        E.add_tag st x (fst (D.get_assign x))
    with E.Unsat (a, b, l) ->
      raise (D.Absurd (mk_expl (a, b, l)))

let eq_assign x =
    D.watch 1 [x] (tag x);
    try
      begin match E.find_tag st x with
        | _, Some (_, v) -> v
        | x, None -> try fst (D.get_assign x) with D.Not_assigned _ -> x
      end
    with E.Unsat (a, b, l) ->
      raise (D.Absurd (mk_expl (a, b, l)))

let eq_assume (f, _) = match f with
  | { Expr.formula = Expr.Equal (a, b)} ->
          wrap E.add_eq a b;
          D.watch 1 [a] (tag a);
          D.watch 1 [b] (tag b);
          D.watch 1 [a; b] (f_eval f)
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b)} } ->
          wrap E.add_neq a b;
          D.watch 1 [a] (tag a);
          D.watch 1 [b] (tag b);
          D.watch 1 [a; b] (f_eval f)
  | _ -> ()

let rec set_handler = function
  | { Expr.term = Expr.Var v } -> Expr.(set_assign v 0 eq_assign)
  | { Expr.term = Expr.Meta m } -> Expr.(set_assign m.meta_var 0 eq_assign)
  | { Expr.term = Expr.Tau t } -> Expr.(set_assign t.tau_var 0 eq_assign)
  | { Expr.term = Expr.App (f, _, l) } ->
    Expr.set_assign f 0 eq_assign;
    List.iter set_handler l

let rec eq_pre = function
  | { Expr.formula = Expr.Equal (a, b) } ->
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
  | { Expr.formula = Expr.All (_, f) }
  | { Expr.formula = Expr.AllTy (_, f) }
  | { Expr.formula = Expr.Ex (_, f) }
  | { Expr.formula = Expr.ExTy (_, f) } ->
    eq_pre f
  | _ -> ()

;;

D.(register {
    name = "eq";
    assume = eq_assume;
    eval_pred = eq_eval;
    preprocess = eq_pre;
  })


