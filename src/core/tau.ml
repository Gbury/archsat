
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()
let st = H.create 256

let mk_proof () = id, "tau", []

let tau = function
    | { Expr.formula = Expr.Ex (l, p) } as f ->
      let taus = Expr.term_taus f in
      let subst = Util.list_fold_product l taus Expr.Subst.empty
        (fun s v t -> Expr.Subst.bind v t s) in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof ())
    | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, p) } } as f ->
      let taus = Expr.term_taus f in
      let subst = Util.list_fold_product l taus Expr.Subst.empty
        (fun s v t -> Expr.Subst.bind v t s) in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof ())
    (* TODO: Taus for types ? *)
    | _ -> ()

let tau_assume (f, i) =
  try
      ignore (H.find st f)
  with Not_found ->
      tau f;
      H.add st f i

let tau_eval _ = None

let tau_pre _ = ()
;;
Dispatcher.(register {
    id = id;
    name = "tau";
    assume = tau_assume;
    eval_pred = tau_eval;
    preprocess = tau_pre;
  })

