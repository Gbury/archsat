
let section = Util.Section.make ~parent:Dispatcher.section "skolem"

module H = Hashtbl.Make(Expr.Formula)

type kind =
  | Tau
  | Skolem

let kind_list = [
  "tau", Tau;
  "skolem", Skolem;
]

let kind_conv = Cmdliner.Arg.enum kind_list

let inst = ref Tau

(* Set-hashtbl to tag translated formulas *)
let seen = H.create 256

let has_been_seen f =
  try ignore (H.find seen f); true
  with Not_found -> false

let mark f = H.add seen f 0

(* Proof generation *)
let mk_proof_ty f p l taus = Dispatcher.mk_proof "skolem"
    ~ty_args:(List.fold_left2 (fun acc a b -> Expr.Ty.of_id a :: b :: acc) [] l taus)
    ~formula_args:[f; p] "skolem-ty"

let mk_proof_term f p l taus = Dispatcher.mk_proof "skolem"
    ~term_args:(List.fold_left2 (fun acc a b -> Expr.Term.of_id a :: b :: acc) [] l taus)
    ~formula_args:[f; p] "skolem-term"

let get_ty_taus ty_args t_args l =
  assert (t_args = []);
  match !inst with
  | Tau -> List.map Expr.(fun v -> Ty.apply (Id.ty_fun ("t_" ^ v.id_name) 0) []) l
  | Skolem -> List.map (fun v -> Expr.Ty.apply (Expr.Id.ty_skolem v) ty_args) l

let get_term_taus ty_args t_args l = match !inst with
  | Tau -> List.map Expr.(fun v -> Term.apply (Id.term_fun ("t_" ^ v.id_name) [] [] v.id_type) [] []) l
  | Skolem -> List.map (fun v -> Expr.Term.apply (Expr.Id.term_skolem v) ty_args t_args) l

let tau = function
  | { Expr.formula = Expr.Ex (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section 10 "New formula %a" Expr.Debug.formula f;
      Util.debug ~section 10 "Free variables: %a ; %a"
        (CCPrint.list Expr.Debug.ty) ty_args
        (CCPrint.list Expr.Debug.term) t_args;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_term f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, (ty_args, t_args), p) } } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section 10 "New formula %a" Expr.Debug.formula f;
      Util.debug ~section 10 "Free variables: %a ; %a"
        (CCPrint.list Expr.Debug.ty) ty_args
        (CCPrint.list Expr.Debug.term) t_args;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_term f (Expr.Formula.neg q) l taus)
    end
  | { Expr.formula = Expr.ExTy (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section 10 "New formula %a" Expr.Debug.formula f;
      Util.debug ~section 10 "Free variables: %a ; %a"
        (CCPrint.list Expr.Debug.ty) ty_args
        (CCPrint.list Expr.Debug.term) t_args;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_ty f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, (ty_args, t_args), p) } } as f ->
    assert (t_args = []);
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section 10 "New formula %a" Expr.Debug.formula f;
      Util.debug ~section 10 "Free variables: %a ; %a"
        (CCPrint.list Expr.Debug.ty) ty_args
        (CCPrint.list Expr.Debug.term) t_args;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_ty f (Expr.Formula.neg q) l taus)
    end
  (* TODO: Taus for types ? *)
  | _ -> ()

let opts =
  let docs = Options.ext_sect in
  let kind =
    let doc = CCPrint.sprintf
        "Decide the strategy to use for existencially quantified variables.
         $(docv) may be %s" (Cmdliner.Arg.doc_alts_enum ~quoted:false kind_list) in
    Cmdliner.Arg.(value & opt kind_conv Skolem & info ["skolem.kind"] ~docv:"KIND" ~docs ~doc)
  in
  let set_opts kind =
    inst := kind
  in
  Cmdliner.Term.(pure set_opts $ kind)

let register () =
  Dispatcher.Plugin.register "skolem" ~options:opts
    ~descr:"Generate skolem or tau for existencially quantified formulas (see options)."
    (Dispatcher.mk_ext ~section ~assume:tau ())

