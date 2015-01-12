
module D = Dispatcher
module U = Ec.Make(Expr.Term)

let state = ref U.empty
let stack = Vector.make 10 U.empty

let eq_assume s =
    try
        for i = D.(s.start) to D.(s.start + s.length - 1) do
          begin match D.(s.get i) with
          | D.Lit {Expr.formula = Expr.Equal (a, b)}, lvl ->
                  state := U.add_eq !state a b
          | D.Lit {Expr.formula = Expr.Not {Expr.formula = Expr.Equal (a, b)}}, lvl ->
                  state := U.add_neq !state a b
          | _ -> ()
          end
        done
    with U.Unsat (x, y, expl) ->
        ()

let eq_assign x = Some (U.find !state x)

;;
D.(register {
    name = "eq";
    assume = (fun _ -> assert false);
    assign = (fun _ -> assert false);
    eval_term = (fun _ -> assert false);
    eval_pred = (fun _ -> None);
    interprets = (fun _ -> false);
    backtrack = (fun i -> Vector.shrink stack (Vector.size stack - i); state := Vector.get stack (i - 1));
    current_level = (fun _ -> Vector.push stack !state; Vector.size stack);
  })

