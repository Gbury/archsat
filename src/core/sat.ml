
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

let sat_assume = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}, lvl ->
    D.set_assign t p_true lvl
  | {Expr.formula = Expr.Not {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}}, lvl ->
    D.set_assign t p_false lvl
  | _ -> ()

let sat_assign = function
  | {Expr.term = Expr.App (p, [], [])} as t when Expr.(Ty.equal t.t_type type_prop) ->
    D.watch 1 [t] (fun () ->
        let v, lvl = D.get_assign t in
        if Expr.Term.equal v p_true then
            D.propagate (Expr.f_pred t) lvl
        else
            D.propagate (Expr.f_not (Expr.f_pred t)) lvl);
    begin try
        fst (D.get_assign t)
      with D.Not_assigned _ ->
        p_true
    end
  | _ -> assert false

let sat_eval = function
  | {Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)} ->
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


let rec sat_preprocess = function
  | { Expr.formula = Expr.Pred ({Expr.term = Expr.App (p, [], [])} as t)}
    when Expr.(Ty.equal t.t_type type_prop) ->
          Expr.set_assign p 0 sat_assign
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
    name = "sat";
    assume = sat_assume;
    eval_pred = sat_eval;
    preprocess = sat_preprocess;
    backtrack = (fun _ -> ());
    current_level = (fun _ -> 0);
  })
