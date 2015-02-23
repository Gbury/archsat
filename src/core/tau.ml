
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()

(* Set-hashtbl to tag translated formulas *)
let seen = H.create 256

let has_been_seen f =
    try ignore (H.find seen f); true
    with Not_found -> false

let mark f lvl = H.add seen f lvl

(* Proof generation *)
let mk_proof_ty f p l taus = Dispatcher.mk_proof
    ~ty_args:(List.fold_left2 (fun acc a b -> Expr.type_var a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "tau"

let mk_proof_term f p l taus = Dispatcher.mk_proof
    ~term_args:(List.fold_left2 (fun acc a b -> Expr.term_var a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "tau"

let tau lvl = function
    | { Expr.formula = Expr.Ex (l, (ty_args, t_args), p) } as f ->
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map (fun v -> Expr.term_app (Expr.get_term_skolem v) ty_args t_args) l in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; q] (mk_proof_term f q l taus)
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, (ty_args, t_args), p) } } as f ->
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map (fun v -> Expr.term_app (Expr.get_term_skolem v) ty_args t_args) l in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_term f (Expr.f_not q) l taus)
      end
    | { Expr.formula = Expr.ExTy (l, (ty_args, t_args), p) } as f ->
      assert (t_args = []);
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map (fun v -> Expr.type_app (Expr.get_ty_skolem v) ty_args) l in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst subst Expr.Subst.empty p in
        Dispatcher.push [Expr.f_not f; q] (mk_proof_ty f q l taus)
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, (ty_args, t_args), p) } } as f ->
      assert (t_args = []);
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map (fun v -> Expr.type_app (Expr.get_ty_skolem v) ty_args) l in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst subst Expr.Subst.empty p in
        Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_ty f (Expr.f_not q) l taus)
      end
    (* TODO: Taus for types ? *)
    | _ -> ()

let tau_assume (f, i) = tau i f

let tau_eval _ = None

let tau_pre _ = ()

;;
Dispatcher.(register {
    id = id;
    name = "tau";
    assume = tau_assume;
    eval_pred = tau_eval;
    preprocess = tau_pre;
    if_sat = (fun _ -> ());
  })

