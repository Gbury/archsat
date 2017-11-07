
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
  | Ty of Expr.formula * Expr.ty list * Expr.formula
  | Term of Expr.formula * Expr.term list * Expr.formula

type Dispatcher.lemma_info += Sk of lemma_info

(* Module initialisation *)
(* ************************************************************************ *)

let kind_conv = Cmdliner.Arg.enum kind_list

let inst = ref Tau

let epsilon_ty, epsilon_term =
  let count = ref 0 in
  let name () = incr count; Format.sprintf "ε_%d" !count in
  (fun () -> Expr.Id.ttype (name ())),
  (fun ty -> Expr.Id.ty (name ()) ty)

(* Dependencies between epsilons/skolems *)
(* ************************************************************************ *)

module Sty = Set.Make(Expr.Ty)
module Sterm = Set.Make(Expr.Term)

(** Here we consider skolems applications as as epsilon terms, as is done
    in coq proof output.

    We want to compute the depencey graph of epsion temrs (i.e which epsilon
    appears in aother epsilon). *)

(** This tag stores the dependency information, and also serves to identify
    epsilons. *)
let deps = Tag.create ()

let rec find_deps_ty (tys, ts) = function
  | { Expr.ty = (Expr.TyVar _ | Expr.TyMeta _) ; _ } -> (tys, ts)
  | { Expr.ty = Expr.TyApp (f, l) } as ty ->
    let tys' = match Expr.Ty.get_tag ty deps with
      | Some _ -> Sty.add ty tys
      | None -> tys
    in
    List.fold_left find_deps_ty (tys',ts) l

let rec find_deps_term (tys, ts) = function
  | { Expr.term = (Expr.Var _ | Expr.Meta _) ; _ } -> (tys, ts)
  | { Expr.term = Expr.App (f, l, l') ; _ } as term ->
    let ts' = match Expr.Term.get_tag term deps with
      | Some _ -> Sterm.add term ts
      | None -> ts
    in
    find_all_deps (tys, ts') l l'

and find_all_deps (tys, ts) l l' =
    List.fold_left find_deps_term (
      List.fold_left find_deps_ty (tys, ts) l) l'

let gen_ty_tau ty_args t_args v =
  let v' = Expr.(Id.ty_fun ("t_" ^ v.id_name) 0) in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Ty.apply v' [] in
  let () = Expr.Ty.tag res deps (tys, ts) in
  res

let gen_ty_skolem ty_args t_args v =
  let v' = Expr.Id.ty_skolem v in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Ty.apply v' ty_args in
  let () = Expr.Ty.tag res deps (tys, ts) in
  res

let gen_term_tau ty_args t_args v =
  let v' = Expr.(Id.term_fun ("t_" ^ v.id_name) [] [] v.id_type) in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Term.apply v' [] [] in
  let () = Expr.Term.tag res deps (tys, ts) in
  res

let gen_term_skolem ty_args t_args v =
  let v' = Expr.Id.term_skolem v in
  let (tys, ts) = find_all_deps (Sty.empty, Sterm.empty) ty_args t_args in
  let res = Expr.Term.apply v' ty_args t_args in
  let () = Expr.Term.tag res deps (tys, ts) in
  res

(* Helpers *)
(* ************************************************************************ *)

let def = Tag.create ()

let seen = H.create 256

let has_been_seen f =
  try ignore (H.find seen f); true
  with Not_found -> false

let mark f = H.add seen f 0

(* instanciate the first var *)
let ty_inst_first ty = function
  | ({ Expr.formula = Expr.ExTy ((x :: _), _, _) } as f)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.AllTy ((x :: _), _, _) } } as f) ->
    Expr.Formula.partial_inst
      (Expr.Subst.Id.bind Expr.Subst.empty x ty)
      Expr.Subst.empty f
  | _ -> assert false

let term_inst_first term = function
  | ({ Expr.formula = Expr.Ex ((x :: _), _, _) } as f)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.All ((x :: _), _, _) } } as f) ->
    Expr.Formula.partial_inst Expr.Subst.empty
      (Expr.Subst.Id.bind Expr.Subst.empty x term) f
  | _ -> assert false

(* Proof generation *)
let mk_proof_ty f q _ taus =
  let _ = List.fold_left (fun f' ty ->
      let () = Expr.Ty.tag ty def f' in
      ty_inst_first ty f') f taus
  in
  Dispatcher.mk_proof "skolem" "skolem-ty" (Sk (Ty (f, taus, q)))

let mk_proof_term f q _ taus =
  let _ = List.fold_left (fun f' term ->
      Util.debug ~section "tagging: %a -> %a"
        Expr.Print.term term Expr.Print.formula f';
      let () = Expr.Term.tag term def f' in
      term_inst_first term f') f taus
  in
  Dispatcher.mk_proof "skolem" "skolem-term" (Sk (Term (f, taus, q)))

let get_ty_taus ty_args t_args l =
  assert (t_args = []);
  match !inst with
  | Tau -> List.map (gen_ty_tau ty_args t_args) l
  | Skolem -> List.map (gen_ty_skolem ty_args t_args) l

let get_term_taus ty_args t_args l = match !inst with
  | Tau -> List.map (gen_term_tau ty_args t_args) l
  | Skolem -> List.map (gen_term_skolem ty_args t_args) l

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
      let q = Expr.Formula.subst ~t_var_map:subst p in
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
      let q = Expr.Formula.subst ~t_var_map:subst p in
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
      let q = Expr.Formula.subst ~ty_var_map:subst p in
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
      let q = Expr.Formula.subst ~ty_var_map:subst p in
      Dispatcher.push [Expr.Formula.neg f; Expr.Formula.neg q] (mk_proof_ty f (Expr.Formula.neg q) l taus)
    end
  | _ -> ()

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Ty (f, l, _) ->
    Some "LIGHTBLUE", (
      List.map (CCFormat.const Dot.Print.ty) l @
      [ CCFormat.const Dot.Print.formula f ]
    )
  | Term (f, l, _) ->
    Some "LIGHTBLUE", (
      List.map (CCFormat.const Dot.Print.term) l @
      [ CCFormat.const Dot.Print.formula f ]
    )

(*
let pp_coq_fun_ex fmt = function
  | ({ Expr.formula = Expr.ExTy ((x :: _), _, _) } as f)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.AllTy ((x :: _), _, _) } } as f) ->
    let s = Expr.Subst.Id.bind Expr.Subst.empty x (Expr.Ty.of_id x) in
    let f' = Expr.Formula.partial_inst s Expr.Subst.empty f in
    Format.fprintf fmt "fun %a => %a" Coq.Print.id x Coq.Print.formula f'
  | ({ Expr.formula = Expr.Ex ((x :: _), _, _) } as f)
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.All ((x :: _), _, _) } } as f) ->
    let s = Expr.Subst.Id.bind Expr.Subst.empty x (Expr.Term.of_id x) in
    let f' = Expr.Formula.partial_inst Expr.Subst.empty s f in
    Format.fprintf fmt "fun %a => %a" Coq.Print.id x Coq.Print.formula f'
  | _ -> assert false

let pp_coq_ty_prelude fmt e =
  let f = CCOpt.get_exn @@ Expr.Id.get_tag e def in
  Format.fprintf fmt "@[<hv 2>Coq.Logic.Epsilon.epsilon@ (inhabits @[<hov>%a@])@ @[<hov 1>(%a)@]@]"
    Coq.Print.ty Synth.ty pp_coq_fun_ex f

let pp_coq_term_prelude fmt e =
  let f = CCOpt.get_exn @@ Expr.Id.get_tag e def in
  Format.fprintf fmt "@[<hv 2>Coq.Logic.Epsilon.epsilon@ (inhabits @[<hov>%a@])@ @[<hov 1>(%a)@]@]"
    Coq.Print.term (Synth.term Expr.(e.id_type)) pp_coq_fun_ex f

let ty_cache = CCCache.unbounded ~eq:Expr.Ty.equal ~hash:Expr.Ty.hash 42
let term_cache = CCCache.unbounded ~eq:Expr.Term.equal ~hash:Expr.Term.hash 42

let rec coq_preludes tys ts =
  Sterm.fold (fun t acc ->
      Coq.Prelude.S.add (coq_term_prelude t) acc) ts
    (Sty.fold (fun ty acc ->
         Coq.Prelude.S.add (coq_ty_prelude ty) acc) tys
        (Coq.Prelude.S.singleton Coq.Prelude.epsilon))

and coq_ty_prelude ty =
  CCCache.with_cache ty_cache (fun ty ->
      let e = epsilon_ty () in
      let () = Expr.Id.tag e def
          (CCOpt.get_exn @@ Expr.Ty.get_tag ty def) in
      let res = Expr.Ty.of_id e in
      let () = Coq.Print.trap_ty ty res in
      match Expr.Ty.get_tag ty deps with
      | None -> assert false
      | Some (tys, ts) ->
        let deps = coq_preludes tys ts in
        Coq.Prelude.abbrev ~deps e pp_coq_ty_prelude
    ) ty

and coq_term_prelude term =
  CCCache.with_cache term_cache (fun term ->
      let e = epsilon_term Expr.(term.t_type) in
      let f = CCOpt.get_exn @@ Expr.Term.get_tag term def in
      let () = Expr.Id.tag e def f in
      Util.debug ~section "def: %a // %a --> %a"
        Expr.Print.id e Expr.Print.term term Expr.Print.formula f;
      let res = Expr.Term.of_id e in
      let () = Coq.Print.trap_term term res in
      match Expr.Term.get_tag term deps with
      | None -> assert false
      | Some (tys, ts) ->
        let deps = coq_preludes tys ts in
        Coq.Prelude.abbrev ~deps e pp_coq_term_prelude
    ) term

let pp_ex is_not_all fmt s =
  if not is_not_all then Format.fprintf fmt "%s" s
  else Format.fprintf fmt "(Coq.Logic.Classical_Pred_Type.not_all_ex_not _ _ %s)" s

let pp_not_ex_not fmt s =
  Format.fprintf fmt "(Coq.Logic.Classical_Pred_Type.not_all_not_ex _ _ %s)" s

let coq_ex_ty is_not_all s fmt _ =
  Format.fprintf fmt "@[<hov 2>Coq.Logic.Epsilon.epsilon_spec@ (inhabits %a) _@ %a@]"
    Coq.Print.ty Synth.ty (pp_ex is_not_all) s

let coq_not_ex_not_ty s fmt _ =
  Format.fprintf fmt "@[<hov 2>Coq.Logic.Epsilon.epsilon_spec@ (inhabits %a) _@ %a@]"
    Coq.Print.ty Synth.ty pp_not_ex_not s

let coq_ex is_not_all s fmt t =
  Format.fprintf fmt "@[<hov 2>Coq.Logic.Epsilon.epsilon_spec@ (inhabits %a) _@ %a@]"
    Coq.Print.term (Synth.term Expr.(t.t_type)) (pp_ex is_not_all) s

let coq_not_ex_not s fmt t =
  Format.fprintf fmt "@[<hov 2>Coq.Logic.Epsilon.epsilon_spec@ (inhabits %a) _@ %a@]"
    Coq.Print.term (Synth.term Expr.(t.t_type)) pp_not_ex_not s

let coq_proof = function
  | Ty ({ Expr.formula = Expr.ExTy _} as f, l, q) ->
    Coq.tactic ~prefix:"Q"
      ~prelude:(Coq.Prelude.epsilon :: List.map coq_ty_prelude l) (fun fmt ctx ->
            let res = Coq.sequence ctx (coq_ex_ty false) (Proof.Ctx.name ctx f) fmt l in
            Coq.exact fmt "%s" res
        )
  | Ty ({ Expr.formula = Expr.Not {Expr.formula = Expr.AllTy (
      _, _, { Expr.formula = Expr.Not _ } ) } } as f, l, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f])
      ~prelude:(Coq.Prelude.epsilon :: Coq.Prelude.classical ::
                List.map coq_ty_prelude l) (fun fmt ctx ->
          let l', last = match CCList.take_drop (List.length l - 1) l with
            | res, [x] -> res, x
            | _ -> assert false
          in
          let tmp = Coq.sequence ctx (coq_ex_ty true) (Proof.Ctx.name ctx f) fmt l' in
          Coq.exact fmt "%a (%a)"
            (Proof.Ctx.named ctx) (Expr.Formula.neg q) (coq_not_ex_not_ty tmp) last
        )
  | Ty ({ Expr.formula = Expr.Not ({Expr.formula = Expr.AllTy _} as f) }, l, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f])
      ~prelude:(Coq.Prelude.epsilon :: Coq.Prelude.classical ::
                List.map coq_ty_prelude l) (fun fmt ctx ->
          let res = Coq.sequence ctx (coq_ex_ty true) (Proof.Ctx.name ctx f) fmt l in
          Coq.exact fmt "%s" res
        )
  | Term ({ Expr.formula = Expr.Ex _} as f, l, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f])
      ~prelude:(Coq.Prelude.epsilon :: List.map coq_term_prelude l) (fun fmt ctx ->
          let res = Coq.sequence ctx (coq_ex false) (Proof.Ctx.name ctx f) fmt l in
          Coq.exact fmt "%a %s" (Proof.Ctx.named ctx) (Expr.Formula.neg q) res
        )
  | Term ({ Expr.formula = Expr.Not {Expr.formula = Expr.All (
      _, _, { Expr.formula = Expr.Not _ } ) } } as f, l, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f])
      ~prelude:(Coq.Prelude.epsilon :: Coq.Prelude.classical ::
                List.map coq_term_prelude l) (fun fmt ctx ->
          let l', last = match CCList.take_drop (List.length l - 1) l with
            | res, [x] -> res, x
            | _ -> assert false
          in
          let tmp = Coq.sequence ctx (coq_ex true) (Proof.Ctx.name ctx f) fmt l' in
          Coq.exact fmt "%a (%a)"
            (Proof.Ctx.named ctx) (Expr.Formula.neg q) (coq_not_ex_not tmp) last
        )
  | Term ({ Expr.formula = Expr.Not {Expr.formula = Expr.All _} } as f, l, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f])
      ~prelude:(Coq.Prelude.epsilon :: Coq.Prelude.classical ::
                List.map coq_term_prelude l) (fun fmt ctx ->
          let res = Coq.sequence ctx (coq_ex true) (Proof.Ctx.name ctx f) fmt l in
          Coq.exact fmt "%a %s" (Proof.Ctx.named ctx) (Expr.Formula.neg q) res
        )
  | _ -> assert false
*)

(* Cmdliner options and registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Sk info -> Some (dot_info info)
  (* | Coq.Tactic Sk info -> Some (coq_proof info) *)
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

