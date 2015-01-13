
module D = Dispatcher
module M = Map.Make(Expr.Term)

let st = Backtrack.base M.empty

let set x y v lvl =
  try
    let z, v', _ = M.find x (Backtrack.top st) in
    if not (Expr.Term.equal v v') then
      raise (D.Absurd ([
          Expr.f_not (Expr.f_equal x y);
          Expr.f_not (Expr.f_equal x z);
          Expr.f_equal y z]))
  with Not_found ->
    Backtrack.update st (M.add x (y, v, lvl))

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
    Some (value (M.find x (Backtrack.top st)))
  with Not_found ->
    Some x

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

;;
D.(register {
    name = "eq";
    assume = eq_assume;
    assign = eq_assign;
    eval_term = (fun _ -> assert false);
    eval_pred = eq_eval;
    interprets = (fun _ -> false);
    backtrack = (fun i -> assert false);
    current_level = (fun _ -> assert false);
  })

