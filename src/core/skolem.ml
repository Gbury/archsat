
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()

type kind =
  | Tau
  | Skolem

let inst = ref Tau

(* Set-hashtbl to tag translated formulas *)
let seen = H.create 256

let has_been_seen f =
  try ignore (H.find seen f); true
  with Not_found -> false

let mark f lvl = H.add seen f lvl

(* Proof generation *)
let mk_proof_ty f p l taus = Dispatcher.mk_proof
    ~ty_args:(List.fold_left2 (fun acc a b -> Expr.type_var a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "skolem"

let mk_proof_term f p l taus = Dispatcher.mk_proof
    ~term_args:(List.fold_left2 (fun acc a b -> Expr.term_var a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "skolem"

let get_ty_taus ty_args t_args l =
  assert (t_args = []);
  match !inst with
  | Tau -> List.map Expr.(fun v -> type_app (type_const ("e_" ^ v.var_name) 0) []) l
  | Skolem -> List.map (fun v -> Expr.type_app (Expr.get_ty_skolem v) ty_args) l

let get_term_taus ty_args t_args l = match !inst with
  | Tau -> List.map Expr.(fun v -> term_app (term_const ("t_" ^ v.var_name) [] [] v.var_type) [] []) l
  | Skolem -> List.map (fun v -> Expr.term_app (Expr.get_term_skolem v) ty_args t_args) l

let tau lvl = function
  | { Expr.formula = Expr.Ex (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof_term f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, (ty_args, t_args), p) } } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.formula_subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_term f (Expr.f_not q) l taus)
    end
  | { Expr.formula = Expr.ExTy (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.formula_subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.f_not f; q] (mk_proof_ty f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, (ty_args, t_args), p) } } as f ->
    assert (t_args = []);
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Var.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.formula_subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof_ty f (Expr.f_not q) l taus)
    end
  (* TODO: Taus for types ? *)
  | _ -> ()

let tau_assume (f, i) = tau i f

let tau_eval _ = None

let tau_pre _ = ()

let opts t =
  let docs = Options.ext_sect in
  let kind =
    let doc = "Decide the strategy to use for existencially quantified variables, available are : skolem, tau" in
    Cmdliner.Arg.(value & opt (enum ["tau", Tau; "skolem", Skolem]) Tau & info ["skolem.kind"] ~docv:"KIND" ~docs ~doc)
  in
  let set_opts kind t =
    inst := kind;
    t
  in
  Cmdliner.Term.(pure set_opts $ kind $ t)
;;
Dispatcher.(register (
    mk_ext
      ~descr:"Generate skolem or tau for existencially quantified formulas (see options)."
      ~assume:tau_assume
      ~eval_pred:tau_eval
      ~preprocess:tau_pre
      ~options:opts id "skolem"
  ))

