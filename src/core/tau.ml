
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()

(* Set-hashtbl to tag translated formulas *)
let seen = H.create 256

let has_been_seen f =
    try ignore (H.find seen f); true
    with Not_found -> false

let mark f lvl = H.add seen f lvl

(* Proof generation *)
let mk_proof f p l taus =
    id, "tau", [f; p], (List.map2 (fun a b -> Builtin.tuple [Expr.term_var a; b]) l taus)

let tau lvl = function
    | { Expr.formula = Expr.Ex (l, p) } as f ->
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map Expr.term_of_tau (Expr.term_taus f) in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; q] (mk_proof f q l taus)
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, p) } } as f ->
      if not (has_been_seen f) then begin
        mark f lvl;
        let taus = List.map Expr.term_of_tau (Expr.term_taus f) in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.bind v t s) Expr.Subst.empty l taus in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof f (Expr.f_not q) l taus)
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
  })

