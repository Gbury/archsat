
let section = Util.Section.make ~parent:Dispatcher.section "prop"

let sat_assume = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} ->
    Dispatcher.set_assign t Builtin.Misc.p_true
  | { Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}} ->
    Dispatcher.set_assign t Builtin.Misc.p_false
  | _ -> ()

let rec sat_eval = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} ->
    begin try
        let b = Dispatcher.get_assign t in
        if Expr.Term.equal Builtin.Misc.p_true b then
          Some (true, [b])
        else if Expr.Term.equal Builtin.Misc.p_false b then
          Some (false, [b])
        else
          assert false
      with Dispatcher.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not f } ->
    CCOpt.map (fun (b, l) -> (not b, l)) (sat_eval f)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "prop"
    ~descr:"Handles consitency of assignments with regards to predicates (i.e functions which returns a Prop)."
    (Dispatcher.mk_ext
       ~section
       ~assume:sat_assume
       ~eval_pred:sat_eval
       ())
