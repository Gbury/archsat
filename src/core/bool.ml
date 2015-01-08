
let mk_prop i =
  let c = Expr.term_const ("p" ^ string_of_int i) [] [] Expr.type_prop in
  Expr.f_pred (Expr.term_app c [] [])
;;

Dispatcher.(register {
    name = "Bool";
    assume = (fun _ -> assert false);
    assign = (fun _ -> assert false);
    eval_term = (fun _ -> assert false);
    eval_pred = (fun _ -> assert false);
    interprets = (fun _ -> assert false);
    backtrack = (fun _ -> assert false);
    current_level = (fun _ -> assert false);
  })
