
module H = Hashtbl.Make(Expr.Formula)

let id = Dispatcher.new_id ()

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

let mark f lvl = H.add seen f lvl

(* Proof generation *)
let mk_proof_ty f p l taus = Dispatcher.mk_proof
    ~ty_args:(List.fold_left2 (fun acc a b -> Expr.Ty.of_id a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "skolem"

let mk_proof_term f p l taus = Dispatcher.mk_proof
    ~term_args:(List.fold_left2 (fun acc a b -> Expr.Term.of_id a :: b :: acc) [] l taus)
    ~formula_args:[f; p] id "skolem"

let get_ty_taus ty_args t_args l =
  assert (t_args = []);
  match !inst with
  | Tau -> List.map Expr.(fun v -> Ty.apply (Id.ty_fun ("t_" ^ v.id_name) 0) []) l
  | Skolem -> List.map (fun v -> Expr.Ty.apply (Expr.Id.ty_skolem v) ty_args) l

let get_term_taus ty_args t_args l = match !inst with
  | Tau -> List.map Expr.(fun v -> Term.apply (Id.term_fun ("t_" ^ v.id_name) [] [] v.id_type) [] []) l
  | Skolem -> List.map (fun v -> Expr.Term.apply (Expr.Id.term_skolem v) ty_args t_args) l

let tau lvl = function
  | { Expr.formula = Expr.Ex (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_term f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, (ty_args, t_args), p) } } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty subst p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_term f (Expr.Formula.neg q) l taus)
    end
  | { Expr.formula = Expr.ExTy (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_ty f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, (ty_args, t_args), p) } } as f ->
    assert (t_args = []);
    if not (has_been_seen f) then begin
      mark f lvl;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s) Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_ty f (Expr.Formula.neg q) l taus)
    end
  (* TODO: Taus for types ? *)
  | _ -> ()

let tau_assume (f, i) = tau i f

let opts t =
  let docs = Options.ext_sect in
  let kind =
    let doc = CCPrint.sprintf
        "Decide the strategy to use for existencially quantified variables.
         $(docv) may be %s" (Cmdliner.Arg.doc_alts_enum ~quoted:false kind_list) in
    Cmdliner.Arg.(value & opt kind_conv Skolem & info ["skolem.kind"] ~docv:"KIND" ~docs ~doc)
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
      ~options:opts id "skolem"
  ))

