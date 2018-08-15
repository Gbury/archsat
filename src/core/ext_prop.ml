
let ext_name = "prop"

let section = Section.make ~parent:Dispatcher.section ext_name

(* Assume & eval *)
(* ************************************************************************ *)

let sat_assume = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)} ->
    Dispatcher.set_assign t Builtin.Misc.p_true
  | { Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, _, _)} as t)}} ->
    Dispatcher.set_assign t Builtin.Misc.p_false
  | _ -> ()

let rec sat_eval = function
  | { Expr.formula = Expr.Pred t} ->
    begin try
        let b = Dispatcher.get_assign t in
        if Expr.Term.equal Builtin.Misc.p_true b then
          Some (true, [t])
        else if Expr.Term.equal Builtin.Misc.p_false b then
          Some (false, [t])
        else begin
          Util.error ~section
            "@[<hv>Term@ %a@ evaluates to@ %a@ which is not a boolean constant"
            Expr.Print.term t Expr.Print.term b;
          assert false
        end
      with Dispatcher.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not f } ->
    CCOpt.map (fun (b, l) -> (not b, l)) (sat_eval f)
  | _ -> None

(* Setup watchers *)
(* ************************************************************************ *)

let watch = Dispatcher.mk_watch (module Expr.Formula) ext_name

let watcher t () =
  match sat_eval t with
  | Some (b, l) ->
    let f = if b then t else Expr.Formula.neg t in
    Dispatcher.propagate f l
  | None ->
    (* this function is called by the watcher, which ensures that t is assigned. *)
    assert false

let set_watcher = function
  | ({ Expr.formula = Expr.Pred t } as f)
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Pred t } as f) } ->
    watch f 1 [t] (watcher f)
  | _ -> ()

(* Register extension *)
(* ************************************************************************ *)

let descr =
  "Handles consitency of assignments with regards to predicates (i.e functions which returns a Prop)."

let register () =
  Dispatcher.Plugin.register ext_name ~descr
    (Dispatcher.mk_ext ~section ~set_watcher ~assume:sat_assume ~eval_pred:sat_eval ())

