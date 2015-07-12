
let section = Util.Section.make ~parent:Dispatcher.section "prop"

let sat_assume = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}, lvl ->
    Dispatcher.set_assign t Builtin.Misc.p_true lvl
  | { Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}}, lvl ->
    Dispatcher.set_assign t Builtin.Misc.p_false lvl
  | _ -> ()

let sat_assign = function
  | { Expr.term = Expr.App (p, _, _) } as t (* when Expr.(Ty.equal t.t_type type_prop) *) ->
    begin try
        fst (Dispatcher.get_assign t)
      with Dispatcher.Not_assigned _ ->
        Builtin.Misc.p_true
    end
  | _ -> assert false

let rec sat_eval = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} ->
    begin try
        let b, lvl = Dispatcher.get_assign t in
        if Expr.Term.equal Builtin.Misc.p_true b then
          Some (true, lvl)
        else if Expr.Term.equal Builtin.Misc.p_false b then
          Some (false, lvl)
        else
          assert false
      with Dispatcher.Not_assigned _ ->
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
  | Some(true, lvl) -> Dispatcher.propagate f lvl
  | Some(false, lvl) -> Dispatcher.propagate (Expr.Formula.neg f) lvl
  | None -> ()

let sat_preprocess = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} as f
    when Expr.(Ty.equal t.t_type Ty.prop) ->
    Expr.Id.set_assign p 5 sat_assign;
    Dispatcher.watch "prop" 1 [t] (f_eval f)
  | _ -> ()

;;
Dispatcher.Plugin.register "prop"
  ~descr:"Handles consitency of assignments with regards to predicates (i.e functions which returns a Prop)."
  (Dispatcher.mk_ext
     ~section
     ~assume:sat_assume
     ~eval_pred:sat_eval
     ~peek:sat_preprocess
     ())
