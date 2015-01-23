
module D = Dispatcher

let sat_assume = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}, lvl ->
    D.set_assign t Builtin.p_true lvl
  | {Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}}, lvl ->
    D.set_assign t Builtin.p_false lvl
  | _ -> ()

let sat_assign = function
  | {Expr.term = Expr.App (p, [], [])} as t when Expr.(Ty.equal t.t_type type_prop) ->
    D.watch 1 [t] (fun () ->
        let v, lvl = D.get_assign t in
        if Expr.Term.equal v Builtin.p_true then
          D.propagate (Expr.f_pred t) lvl
        else
          D.propagate (Expr.f_not (Expr.f_pred t)) lvl);
    begin try
        fst (D.get_assign t)
      with D.Not_assigned _ ->
        Builtin.p_true
    end
  | _ -> assert false

let sat_eval = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)} ->
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
  | { Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)} } ->
    begin try
        let b, lvl = D.get_assign t in
        if Expr.Term.equal Builtin.p_true b then
          Some (false, lvl)
        else if Expr.Term.equal Builtin.p_false b then
          Some (true, lvl)
        else
          assert false
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

let rec sat_preprocess = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}
    when Expr.(Ty.equal t.t_type type_prop) ->
    Expr.set_assign p 5 sat_assign
  | { Expr.formula = Expr.Not f } ->
    sat_preprocess f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter sat_preprocess l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    sat_preprocess p;
    sat_preprocess q
  | { Expr.formula = Expr.All (_, f) }
  | { Expr.formula = Expr.AllTy (_, f) }
  | { Expr.formula = Expr.Ex (_, f) } ->
    sat_preprocess f
  | _ -> ()

;;
D.(register {
    name = "prop";
    assume = sat_assume;
    eval_pred = sat_eval;
    preprocess = sat_preprocess;
  })
