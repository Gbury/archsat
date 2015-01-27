
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()
let st = H.create 256

let mk_proof () = id, "meta", []

let meta = function
    | { Expr.formula = Expr.All (l, p) } as f ->
      let metas = Expr.term_metas f in
      let subst = Util.list_fold_product l metas Expr.Subst.empty
        (fun s v t -> Expr.Subst.bind v t s) in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof ())
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, p) } } as f ->
      let metas = Expr.term_metas f in
      let subst = Util.list_fold_product l metas Expr.Subst.empty
        (fun s v t -> Expr.Subst.bind v t s) in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof ())
    | _ -> ()
    (* TODO: Type metas *)

let meta_assume (f, i) =
  try
      ignore (H.find st f)
  with Not_found ->
      meta f;
      H.add st f i

let meta_eval _ = None

let meta_pre _ = ()
;;
Dispatcher.(register {
    id = id;
    name = "meta";
    assume = meta_assume;
    eval_pred = meta_eval;
    preprocess = meta_pre;
  })

