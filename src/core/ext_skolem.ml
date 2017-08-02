
let section = Section.make ~parent:Dispatcher.section "skolem"

(* Module & types *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Formula)

type kind =
  | Tau
  | Skolem

let kind_list = [
  "tau", Tau;
  "skolem", Skolem;
]

type lemma_info =
  | Ty of Expr.formula * Expr.ty list
  | Term of Expr.formula * Expr.term list

type Dispatcher.lemma_info += Sk of lemma_info

(* Module initialisation *)
(* ************************************************************************ *)

let kind_conv = Cmdliner.Arg.enum kind_list

let inst = ref Tau

(* Helpers *)
(* ************************************************************************ *)

let seen = H.create 256

let has_been_seen f =
  try ignore (H.find seen f); true
  with Not_found -> false

let mark f = H.add seen f 0

(* Proof generation *)
let mk_proof_ty f _ _ taus =
  Dispatcher.mk_proof "skolem" "skolem-ty" (Sk (Ty (f, taus)))

let mk_proof_term f _ _ taus =
  Dispatcher.mk_proof "skolem" "skolem-term" (Sk (Term (f, taus)))

let get_ty_taus ty_args t_args l =
  assert (t_args = []);
  match !inst with
  | Tau -> List.map Expr.(fun v -> Ty.apply (Id.ty_fun ("t_" ^ v.id_name) 0) []) l
  | Skolem -> List.map (fun v -> Expr.Ty.apply (Expr.Id.ty_skolem v) ty_args) l

let get_term_taus ty_args t_args l = match !inst with
  | Tau -> List.map Expr.(fun v -> Term.apply (Id.term_fun ("t_" ^ v.id_name) [] [] v.id_type) [] []) l
  | Skolem -> List.map (fun v -> Expr.Term.apply (Expr.Id.term_skolem v) ty_args t_args) l

(* Helpers *)
(* ************************************************************************ *)

let tau = function
  | { Expr.formula = Expr.Ex (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula:@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Print.formula f
            (CCFormat.list Expr.Print.ty) ty_args
            (CCFormat.list Expr.Print.term) t_args;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty Expr.Subst.empty subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_term f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, (ty_args, t_args), p) } } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula:@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Print.formula f
            (CCFormat.list Expr.Print.ty) ty_args
            (CCFormat.list Expr.Print.term) t_args;
      let taus = get_term_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst Expr.Subst.empty Expr.Subst.empty subst Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_term f (Expr.Formula.neg q) l taus)
    end
  | { Expr.formula = Expr.ExTy (l, (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula:@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Print.formula f
            (CCFormat.list Expr.Print.ty) ty_args
            (CCFormat.list Expr.Print.term) t_args;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty Expr.Subst.empty Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof_ty f q l taus)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, (ty_args, t_args), p) } } as f ->
    assert (t_args = []);
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula:@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Print.formula f
            (CCFormat.list Expr.Print.ty) ty_args
            (CCFormat.list Expr.Print.term) t_args;
      let taus = get_ty_taus ty_args t_args l in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty l taus in
      let q = Expr.Formula.subst subst Expr.Subst.empty Expr.Subst.empty Expr.Subst.empty p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_ty f (Expr.Formula.neg q) l taus)
    end
  | _ -> ()

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Ty (f, l) ->
    Some "LIGHTBLUE", (
      List.map (CCFormat.const Dot.Print.ty) l @
      [ CCFormat.const Dot.Print.formula f ]
    )
  | Term (f, l) ->
    Some "LIGHTBLUE", (
      List.map (CCFormat.const Dot.Print.term) l @
      [ CCFormat.const Dot.Print.formula f ]
    )


(* Cmdliner options and registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Sk info -> Some (dot_info info)
  | _ -> None

let opts =
  let docs = Options.ext_sect in
  let kind =
    let doc = Format.asprintf
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
    (Dispatcher.mk_ext ~section ~assume:tau ~handle:{Dispatcher.handle} ())

