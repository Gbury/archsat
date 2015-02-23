
module D = Dispatcher

let id = D.new_id ()

let sat_assume = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}, lvl ->
    D.set_assign t Builtin.p_true lvl
  | { Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}}, lvl ->
    D.set_assign t Builtin.p_false lvl
  | _ -> ()

let sat_assign = function
  | { Expr.term = Expr.App (p, _, _) } as t (* when Expr.(Ty.equal t.t_type type_prop) *) ->
    begin try
        fst (D.get_assign t)
      with D.Not_assigned _ ->
        Builtin.p_true
    end
  | _ -> assert false

let rec sat_eval = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} ->
    begin try
        let b, lvl = D.get_assign t in
        if Expr.Term.equal Builtin.p_true b then
          Some (true, lvl)
        else if Expr.Term.equal Builtin.p_false b then
          Some (false, lvl)
        else
          assert false
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not f } ->
    begin match sat_eval f with
      | None -> None
      | Some (b, lvl) -> Some (not b, lvl)
    end
  | _ -> None

let f_eval f () =
    match sat_eval f with
    | Some(true, lvl) -> D.propagate f lvl
    | Some(false, lvl) -> D.propagate (Expr.f_not f) lvl
    | None -> ()

let rec sat_preprocess = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} as f
    when Expr.(Ty.equal t.t_type type_prop) ->
    Expr.set_assign p 5 sat_assign;
    D.watch id 1 [t] (f_eval f)
  | { Expr.formula = Expr.Not f } ->
    sat_preprocess f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter sat_preprocess l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    sat_preprocess p;
    sat_preprocess q
  | { Expr.formula = Expr.All (_, _, f) }
  | { Expr.formula = Expr.AllTy (_, _, f) }
  | { Expr.formula = Expr.Ex (_, _, f) } ->
    sat_preprocess f
  | _ -> ()

;;
D.(register {
    id = id;
    name = "prop";
    assume = sat_assume;
    eval_pred = sat_eval;
    preprocess = sat_preprocess;
    if_sat = (fun _ -> ());
  })
