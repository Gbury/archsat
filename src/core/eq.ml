
module D = Dispatcher
module M = Backtrack.HashtblBack(Expr.Term)

let st = M.create D.stack

let set x y v lvl =
  try
    let z, v', _ = M.find st x in
    if not (Expr.Term.equal v v') then
      raise (D.Absurd ([
          Expr.f_not (Expr.f_equal x y);
          Expr.f_not (Expr.f_equal x z);
          Expr.f_equal y z]))
  with Not_found ->
    M.add st x (y, v, lvl)

let rec treat a b () =
  try
    let vb, lvl_b = D.get_assign b in
    begin try
        let va, lvl_a = D.get_assign a in
        assert (Expr.Term.equal va vb)
      with D.Not_assigned _ ->
        set a b vb lvl_b
    end
  with D.Not_assigned _ ->
    treat b a ()
(* Potentially dangerous, but since 'treat' is only called by the watching scheme
 * when either a or b is assigned, it shouldn't cause a pb *)

let eq_assume = function
  | { Expr.formula = Expr.Equal (a, b)}, _ -> D.watch 2 [a; b] (treat a b)
  | _ -> ()

let value (_, x, _) = x

let eq_assign x =
  try
    value (M.find st x)
  with Not_found ->
    x

let eq_eval = function
  | {Expr.formula = Expr.Equal (a, b)} ->
    begin try
        let a', lvl_a = D.get_assign a in
        let b', lvl_b = D.get_assign b in
        Some (Expr.Term.equal a' b', max lvl_a lvl_b)
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

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
  | { Expr.formula = Expr.Ex (_, f) } ->
    eq_pre f
  | _ -> ()

;;

D.(register {
    name = "eq";
    assume = eq_assume;
    eval_pred = eq_eval;
    preprocess = eq_pre;
  })


