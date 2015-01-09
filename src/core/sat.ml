
module D = Dispatcher

let p_true = Expr.term_app (Expr.term_const "true" [] [] Expr.type_prop) [] []
let p_false = Expr.term_app (Expr.term_const "false" [] [] Expr.type_prop) [] []

let mk_prop i =
  let aux i =
    let c = Expr.term_const ("p" ^ string_of_int i) [] [] Expr.type_prop in
    Expr.f_pred (Expr.term_app c [] [])
  in
  if i >= 0 then
      aux i
  else
      Expr.f_not (aux ~-i)
;;

let sat_assume s =
    for i = D.(s.start) to D.(s.start + s.length - 1) do
        match D.(s.get i) with
        | D.Lit {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}, lvl ->
                D.set_assign t p_true lvl
        | D.Lit {Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}}, lvl ->
                D.set_assign t p_false lvl
        | _ -> ()
    done

let sat_assign = function
    | {Expr.term = Expr.App (p, [], [])} -> Some (p_true)
    | _ -> None

let sat_eval = function
    | {Expr.term = Expr.App (p, [], [])} as t ->
        begin try
            let b, lvl = D.get_assign t in
            if Expr.Term.equal p_true b then
                Some (true, lvl)
            else if Expr.Term.equal p_false b then
                Some (false, lvl)
            else
                assert false
        with D.Not_assigned _ ->
            None
        end
    | _ -> None

;;

Dispatcher.(register {
    name = "sat";
    assume = sat_assume;
    assign = sat_assign;
    eval_term = (fun _ -> assert false);
    eval_pred = sat_eval;
    interprets = (fun _ -> false);
    backtrack = (fun _ -> ());
    current_level = (fun _ -> 0);
  })
