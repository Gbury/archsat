
module H = Backtrack.HashtblBack(Expr.Term)

let st = H.create Dispatcher.stack

let set_interpretation t () = match t with
  | { Expr.term = Expr.App (f, tys, l) } ->
    let t_v, _ = Dispatcher.get_assign t in
    let l' = List.map (fun x -> fst (Dispatcher.get_assign x)) l in
    let u = Expr.term_app f tys l' in
    begin try
        let t', u_v = H.find st u in
        if not (Expr.Term.equal t_v u_v) then
            begin match t' with
            | { Expr.term = Expr.App (_, _, r) } ->
              let eqs = List.map2 (fun a b -> Expr.f_not (Expr.f_equal a b)) l r in
              raise (Dispatcher.Absurd ((Expr.f_equal t t') :: eqs, "eq"))
            | _ -> assert false
            end
    with Not_found ->
        H.add st u (t, t_v)
    end
  | _ -> assert false


let rec set_handler = function
  | { Expr.term = Expr.Var _ }
  | { Expr.term = Expr.Meta _ }
  | { Expr.term = Expr.Tau _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    List.iter set_handler l;
    if l <> [] && not Expr.(Ty.equal f.var_type.fun_ret type_prop) then
        Dispatcher.watch 1 (t :: l) (set_interpretation t)

let rec uf_pre = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    set_handler a;
    set_handler b
  | { Expr.formula = Expr.Pred p } ->
    set_handler p
  | { Expr.formula = Expr.Not f } ->
    uf_pre f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter uf_pre l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    uf_pre p;
    uf_pre q
  | { Expr.formula = Expr.All (_, f) }
  | { Expr.formula = Expr.AllTy (_, f) }
  | { Expr.formula = Expr.Ex (_, f) }
  | { Expr.formula = Expr.ExTy (_, f) } ->
    uf_pre f
  | _ -> ()

;;
Dispatcher.(register {
    name = "uf";
    assume = (fun _ -> ());
    eval_pred = (fun _ -> None);
    preprocess = uf_pre;
  })
