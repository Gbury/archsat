
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
  | Inst of Expr.formula * Expr.ty list * Expr.term list * Expr.formula

type Dispatcher.lemma_info += Sk of lemma_info

(* Module initialisation *)
(* ************************************************************************ *)

let kind_conv = Cmdliner.Arg.enum kind_list

let inst = ref Tau

let epsilon_name =
  let count = ref 0 in
  (fun () -> incr count; Format.sprintf "ε_%d" !count)

(* Dependencies between epsilons/skolems *)
(* ************************************************************************ *)

module Sty = Set.Make(Expr.Ty)
module Sterm = Set.Make(Expr.Term)

(** Here we consider skolems applications as as epsilon terms, as is done
    in coq proof output.

    We want to compute the depency graph of epsilon terms (i.e which epsilon
    appears in another epsilon). *)

(** This tag stores the dependency information, and also serves to identify
    epsilons. *)
let dep_tag = Tag.create ()

let rec find_deps_ty (tys, ts) = function
  | { Expr.ty = (Expr.TyVar _ | Expr.TyMeta _) ; _ } -> (tys, ts)
  | { Expr.ty = Expr.TyApp (f, l) } as ty ->
    let tys' = match Expr.Ty.get_tag ty dep_tag with
      | Some _ -> Sty.add ty tys
      | None -> tys
    in
    List.fold_left find_deps_ty (tys',ts) l

let rec find_deps_term (tys, ts) = function
  | { Expr.term = (Expr.Var _ | Expr.Meta _) ; _ } -> (tys, ts)
  | { Expr.term = Expr.App (f, l, l') ; _ } as term ->
    let ts' = match Expr.Term.get_tag term dep_tag with
      | Some _ -> Sterm.add term ts
      | None -> ts
    in
    find_all_deps (tys, ts') l l'

and find_all_deps (tys, ts) l l' =
    List.fold_left find_deps_term (
      List.fold_left find_deps_ty (tys, ts) l) l'

(* Proof generation *)
let prelude_tag = Tag.create ()

let prelude_of_deps (tys, ts) =
  Sterm.fold (fun t l ->
      CCOpt.get_exn (Expr.Term.get_tag t prelude_tag) :: l
    ) ts @@
  Sty.fold (fun ty l ->
      CCOpt.get_exn (Expr.Ty.get_tag ty prelude_tag) :: l
    ) tys [Quant.epsilon_prelude]

let inst_epsilon get_tag tag trap inhabited e t =
  match Quant.match_ex t with
  | Some (x, body) ->
    let p = Term.lambda x body in
    let eps_term = Term.apply Quant.epsilon_term [x.Expr.id_type; inhabited; p] in
    let eps = Term.define (epsilon_name ()) eps_term in
    let eps_t = Term.id eps in
    let deps = prelude_of_deps @@ CCOpt.get_exn @@ get_tag e dep_tag in
    let alias = Proof.Prelude.alias ~deps eps (fun _ -> Some eps_term) in
    let () = tag e prelude_tag alias in
    let () = trap e eps_t in
    Term.(subst (S.Id.bind S.empty x eps_t)) body
  | _ ->
    begin match CCOpt.(Logic.match_not t >>= Quant.match_all) with
      | Some (x, body) ->
        let body =
          match Logic.match_not body with
          | Some body' -> body' | None -> Term.app Term.not_term body
        in
        let p = Term.lambda x body in
        let eps_term = Term.apply Quant.epsilon_term [x.Expr.id_type; inhabited; p] in
        let eps = Term.define (epsilon_name ()) eps_term in
        let eps_t = Term.id eps in
        let deps = prelude_of_deps @@ CCOpt.get_exn @@ get_tag e dep_tag in
        let alias = Proof.Prelude.alias ~deps eps (fun _ -> Some eps_term) in
        let () = tag e prelude_tag alias in
        let () = trap e eps_t in
        Term.(subst (S.Id.bind S.empty x eps_t)) body
      | _ ->
        Util.error ~section
          "@[<hv>Expected an existencial (or not_all) but got: @[<hov>%a@]@]" Term.print t;
        assert false
    end

let mk_proof f q types terms =
  Util.debug ~section "mk_proof: @[<v>%a@ [@[<hov>%a]@]@ [@[<hov>%a]@]@ %a@]"
    Expr.Formula.print f
    CCFormat.(list ~sep:(return ";@ ") Expr.Ty.print) types
    CCFormat.(list ~sep:(return ";@ ") Expr.Term.print) terms
    Expr.Formula.print q;
  let t = Term.of_formula f in
  let t = List.fold_left (fun t e ->
      let inhabited = Term.apply Quant.inhabits_term
          [Term._Type; Term.of_ty ~callback:Prove.add_implicit Synth.ty] in
      inst_epsilon Expr.Ty.get_tag Expr.Ty.tag Term.trap_ty inhabited e t
    ) t types in
  let t = List.fold_left (fun t e ->
      let e_ty = e.Expr.t_type in
      Util.debug ~section "  |- @[<hv>%a :@ %a@]"
        Expr.Term.print e Expr.Ty.print e_ty;
      let inhabited = Term.apply Quant.inhabits_term
          [Term.of_ty e_ty; Term.of_term ~callback:Prove.add_implicit @@ Synth.term e_ty] in
      inst_epsilon Expr.Term.get_tag Expr.Term.tag Term.trap_term inhabited e t
    ) t terms in
  assert (Term.Reduced.equal t (Term.of_formula q));
  Dispatcher.mk_proof "skolem" "inst" (Sk (Inst (f, types, terms, q)))


(* Generating tau and metas *)
(* ************************************************************************ *)

let tau_counter = ref 0

let gen_ty_tau ~status ty_args t_args v =
  let () = incr tau_counter in
  let v' = Expr.(Id.ty_fun (Format.sprintf "τ%d" !tau_counter) 0) in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Ty.apply ~status v' [] in
  let () = Expr.Ty.tag res dep_tag (tys, ts) in
  res

let gen_ty_skolem ~status ty_args t_args v =
  let v' = Expr.Id.ty_skolem v in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Ty.apply ~status v' ty_args in
  let () = Expr.Ty.tag res dep_tag (tys, ts) in
  res

let gen_term_tau ~status m ty_args t_args v =
  let () = incr tau_counter in
  let ty = Mapping.apply_ty m v.Expr.id_type in
  let v' = Expr.(Id.term_fun (Format.sprintf "τ%d" !tau_counter) [] [] ty) in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Term.apply ~status v' [] [] in
  let () = Expr.Term.tag res dep_tag (tys, ts) in
  res

let gen_term_skolem ~status ty_args types t_args v =
  let v' = Expr.Id.term_skolem v in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Term.apply ~status v' (ty_args @ types) t_args in
  let () = Expr.Term.tag res dep_tag (tys, ts) in
  res

(* Helpers *)
(* ************************************************************************ *)

let seen = H.create 256

let has_been_seen f =
  try ignore (H.find seen f); true
  with Not_found -> false

let mark f = H.add seen f 0

let get_ty_taus ~status ty_args t_args l =
  match !inst with
  | Tau -> List.map (gen_ty_tau ~status ty_args t_args) l
  | Skolem -> List.map (gen_ty_skolem ~status ty_args t_args) l

let get_term_taus ~status m ty_args types t_args l = match !inst with
  | Tau -> List.map (gen_term_tau ~status m ty_args t_args) l
  | Skolem -> List.map (gen_term_skolem ~status ty_args types t_args) l

(* Helpers *)
(* ************************************************************************ *)

let tau = function
  | { Expr.formula = Expr.Ex ((l, l'), (ty_args, t_args), p) } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula (%a):@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Status.print f.Expr.f_status Expr.Print.formula f
        (CCFormat.list Expr.Print.ty) ty_args
        (CCFormat.list Expr.Print.term) t_args;
      let types = get_ty_taus ~status:f.Expr.f_status ty_args t_args l in
      let m = List.fold_left2 Mapping.Var.bind_ty Mapping.empty l types in
      let terms = get_term_taus ~status:f.Expr.f_status m ty_args types t_args l' in
      let m = List.fold_left2 Mapping.Var.bind_term m l' terms in
      let q = Mapping.apply_formula m p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof f q types terms)
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All ((l, l'), (ty_args, t_args), p) } } as f ->
    if not (has_been_seen f) then begin
      mark f;
      Util.debug ~section "@[<hov 2>New formula (%a):@ %a@\nwith free variables:@ %a,@ %a"
        Expr.Status.print f.Expr.f_status Expr.Print.formula f
        (CCFormat.list Expr.Print.ty) ty_args
        (CCFormat.list Expr.Print.term) t_args;
      let types = get_ty_taus ~status:f.Expr.f_status ty_args t_args l in
      let m = List.fold_left2 Mapping.Var.bind_ty Mapping.empty l types in
      let terms = get_term_taus ~status:f.Expr.f_status m ty_args types t_args l' in
      let m = List.fold_left2 Mapping.Var.bind_term m l' terms in
      let q = Expr.Formula.neg @@ Mapping.apply_formula m p in
      Dispatcher.push [Expr.Formula.neg f; q] (mk_proof f q types terms)
    end
  | _ -> ()

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Inst (f, l, l', _) ->
    Some "LIGHTBLUE", (
      List.map (CCFormat.const Dot.Print.ty) l @
      List.map (CCFormat.const Dot.Print.term) l' @
      [ CCFormat.const Dot.Print.formula f ]
    )

let coq_proof = function
  | Inst ( { Expr.formula = Expr.Ex _ } as f, tys, ts, res) ->
    (** We want to prove ~ ~ [ exists _, body] -> ~ body -> False,
        note that [body] may be a negation. *)
    let deps = List.map (fun ty -> CCOpt.get_exn @@ Expr.Ty.get_tag ty prelude_tag) tys @
               List.map (fun t -> CCOpt.get_exn @@ Expr.Term.get_tag t prelude_tag) ts in
    let args = List.map Term.of_ty tys @
               List.map Term.of_term ts in
    let witnesses = List.map (fun _ -> Term.of_ty Synth.ty) tys @
                    List.map (fun t -> Term.of_term @@ Synth.term t.Expr.t_type) ts in
    let l = List.combine args witnesses in
    (fun pos -> pos
                |> Logic.introN "Q" 2
                |> Logic.not_not_elim "Q" (Term.of_formula f)
                |> Logic.find (Term.app Term.not_term @@ Term.of_formula res) (Logic.apply1 [])
                |> Logic.find (Term.of_formula f) @@ (fun f ->
                    Logic.exact (Quant.epsilon_prelude :: deps) (Quant.inst_epsilon f l))
    )
  | Inst ( { Expr.formula = Expr.Not {
      Expr.formula = Expr.All _ } } as f, tys, ts, res) ->
    (** We want to prove ~ [ all _, body] -> ~ ~ body -> False (res = ~ body)
                      or ~ [ all _, ~ body] -> ~ body -> False (res = body) *)
    let deps = List.map (fun ty -> CCOpt.get_exn @@ Expr.Ty.get_tag ty prelude_tag) tys @
               List.map (fun t -> CCOpt.get_exn @@ Expr.Term.get_tag t prelude_tag) ts in
    let args = List.map Term.of_ty tys @
               List.map Term.of_term ts in
    let witnesses = List.map (fun _ -> Term.of_ty Synth.ty) tys @
                    List.map (fun t -> Term.of_term @@ Synth.term t.Expr.t_type) ts in
    let l = List.combine args witnesses in
    (fun pos -> pos
                |> Logic.introN "Q" 2
                |> Logic.find (Term.app Term.not_term @@ Term.of_formula res) (Logic.apply1 [])
                |> Logic.find (Term.of_formula f) @@ (fun f ->
                    Logic.exact (Logic.classical :: Quant.epsilon_prelude :: deps) (Quant.inst_epsilon f l))
    )

  | _ -> assert false

(* Cmdliner options and registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Sk info -> Some (dot_info info)
  | Proof.Lemma Sk info -> Some (coq_proof info)
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

