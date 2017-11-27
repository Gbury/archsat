
(* Extension name *)
let name = "rwrt"

(* Module initialisation *)
(* ************************************************************************ *)

module C = Ext_eq.Class
module T = CCSet.Make(C)
module S = Set.Make(Expr.Term)

module H = Hashtbl.Make(Expr.Term)
module M = Hashtbl.Make(Expr.Id.Const)

let section = Section.make ~parent:Dispatcher.section "rwrt"
let section_trigger = Section.make ~parent:section "trigger"
let section_subst = Section.make ~parent:section "subst"

let tag = Tag.create ()

type lemma_info = Subst of Expr.term * Rewrite.Rule.t list

type Dispatcher.lemma_info += Rewrite of lemma_info

(* Plugin state *)
(* ************************************************************************ *)

let inactive_rules = ref []
let active_subst_rules = ref []
let active_trigger_rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack inactive_rules
let () = Backtrack.Stack.attach Dispatcher.stack active_subst_rules
let () = Backtrack.Stack.attach Dispatcher.stack active_trigger_rules

type mode =
  | Auto
  | Manual

let current_mode () =
  match !active_subst_rules, !active_trigger_rules with
  | [], [] -> None
  | r :: _, _
  | _, r :: _ ->
    Some (if Rewrite.Rule.is_manual r then Manual else Auto)

let allow_mixed = ref false

(* Splitting rewrite rules *)
(* ************************************************************************ *)

type rule_type =
  | Trigger
  | Substitution

let split r =
  match r.Rewrite.Rule.trigger with
  | Rewrite.Trigger.Equal _ -> Trigger
  | Rewrite.Trigger.Single _ ->
    begin match r.Rewrite.Rule.result with
      | Rewrite.Rule.Term _ -> Substitution
      | Rewrite.Rule.Formula _ -> Trigger
    end

(* Callbacks on the set of known terms *)
(* ************************************************************************ *)

let add_callback, call =
  let r = ref [] in
  (fun f -> r := f :: !r),
  (fun top t -> List.iter (fun f -> f top t) !r)

(* Some printing functions *)
(* ************************************************************************ *)

let print_matching_aux fmt (t, s) =
  Format.fprintf fmt "@[<hov>%a@ =?@[<hv>%a@]@]"
    Expr.Print.term t CCFormat.(list ~sep:(return ",@ ") C.print) s

let print_matching fmt l =
  Format.fprintf fmt "@[<hv>%a@]"
    CCFormat.(list ~sep:(return ";@ ") print_matching_aux) l

(* Registering parent-child relations between terms *)
(* ************************************************************************ *)

let checked = Tag.create ()
let parents = H.create 42
let index = M.create 42

let index_is_empty () =
  M.length index = 0

let find_parents t =
  try H.find parents t
  with Not_found -> S.empty

let find_index f =
  try M.find index f
  with Not_found -> S.empty

let add_parent parent child =
  let s = find_parents child in
  H.replace parents child (S.add parent s)

let add_to_index top f t =
  call top t;
  let s = find_index f in
  M.replace index f (S.add t s)

let rec register top = function
  (* If the term has already been treated, nothing to do. *)
  | t when Expr.Term.get_tag t checked = Some () -> ()
  (* Else: *)
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    List.iter (add_parent t) l;
    add_to_index top f t;
    Expr.Term.tag t checked ();
    List.iter (register false) l

let find_all_parents t =
  let q = Queue.create () in
  let rec aux acc =
    if Queue.is_empty q then acc
    else begin
      let c = Queue.take q in
      let s = C.fold (fun s x ->
          let parents = find_parents x in
          S.fold aux_single parents s
        ) acc c in
      aux s
    end
  and aux_single y set =
    let d = C.find y in
    if T.mem d set then set
    else begin
      Queue.add d q;
      T.add d set
    end
  in
  aux (aux_single t T.empty)

let find_indexed f =
  let s = find_index f in
  S.fold (fun t acc -> T.add (C.find t) acc) s T.empty

let find_all_indexed ty =
  Util.debug ~section "Finding all indexed terms of type:@ %a" Expr.Print.ty ty;
  M.fold (fun f s acc ->
      Util.debug ~section "Examining term indexed by: %a" Expr.Print.const_ty f;
      match Match.ty Mapping.empty Expr.(f.id_type.fun_ret) ty with
      | _ ->
        S.fold (fun t acc ->
            if Expr.Ty.equal Expr.(t.t_type) ty
            then begin
              Util.debug ~section "Adding:@ %a" Expr.Print.term t;
              T.add (C.find t) acc
            end else begin
              Util.debug ~section "Skipping:@ %a" Expr.Print.term t;
              acc
            end
          ) s acc
      | exception Match.Impossible_ty _ ->
        Util.debug ~section "Types incompatible";
        acc)
    index T.empty

(* Matching modulo equivalence classes *)
(* ************************************************************************ *)

let match_types pats args subst =
  try Some (List.fold_left2 Match.ty subst pats args)
  with
  | Match.Impossible_term _ -> assert false
  | Match.Impossible_ty (a, b) ->
    None

let match_modulo_var v c subst =
  match Mapping.Var.get_term_opt subst v with
  | None ->
    begin try
        let tmp = Match.ty subst Expr.(v.id_type) Expr.(c.t_type) in
        Some (Mapping.Var.bind_term tmp v c)
      with Match.Impossible_ty _ ->
        None
    end
  | Some d ->
    if Expr.Term.equal c d then
      Some subst
    else
      None

let rec match_modulo_app f acc (ty_pats, pats) = function
  | { Expr.term = Expr.App (f', ty_args, args) } ->
    assert (Expr.Id.equal f f');
    let acc' = CCList.filter_map (match_types ty_pats ty_args) acc in
    let l = List.map C.find args in
    List.fold_left2 match_modulo_aux acc' pats l
  | _ -> assert false

and match_modulo_aux acc pat c =
  match pat with
  | { Expr.term = Expr.Var v } ->
    CCList.filter_map (match_modulo_var v (C.repr c)) acc
  | { Expr.term = Expr.Meta _ } as t ->
    if C.mem c t then acc else []
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let l = C.find_top c f in
    CCList.flat_map (match_modulo_app f acc (ty_pats, pats)) l

let match_modulos l =
  List.fold_left (fun acc (t, s) ->
      Util.debug ~section "@[<hv 2>mm:@ @[<hov>%a@]@ @[<hv 4>=? [%a]@];@ @[<hv 2>{ %a }@]@]"
        Expr.Print.term t
        CCFormat.(list ~sep:(return ";@ ") C.print) s
        CCFormat.(list ~sep:(return ";@ ") Mapping.print) acc;
      CCList.flat_map (match_modulo_aux acc t) s
    ) [Mapping.empty] l

let match_modulo = match_modulo_aux [Mapping.empty]

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

(* Parse an arbitrary formula as a rewrite rule *)
let parse_guard = function
  | { Expr.formula = Expr.Pred p } ->
    Some (Rewrite.Guard.Pred_true p)
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred p } } ->
    Some (Rewrite.Guard.Pred_false p)
  | { Expr.formula = Expr.Equal (a, b) } ->
    Some (Rewrite.Guard.Eq (a, b))
  | _ -> None

let parse_guards = function
  | { Expr.formula = Expr.And l } ->
    CCOpt.sequence_l (List.map parse_guard l)
  | f ->
    CCOpt.map (fun x -> [x]) (parse_guard f)

let parse_result = function
  | { Expr.formula = Expr.Pred t } -> Rewrite.Rule.Term t
  | f -> Rewrite.Rule.Formula f

(* Parse manually oriented rules *)
let rec parse_manual_rule = function
  (* Standard rewrite rules *)
  | ({ Expr.formula = Expr.Equal (a, b) } as f) ->
    let trigger, result =
      match Expr.Formula.get_tag f Expr.t_order with
      | None -> assert false
      | Some Expr.Same -> a, b
      | Some Expr.Inverse -> b, a
    in
    Some Rewrite.(Rule.mk true (Trigger.Single trigger) (Rule.Term result))
  | { Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Equal (a, b) }, f) } ->
    Some Rewrite.(Rule.mk true (Trigger.Equal (a, b)) (parse_result f))
  | { Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Pred trigger }, f) } ->
    Some (Rewrite.Rule.mk true (Rewrite.Trigger.Single trigger) (parse_result f))

  (* Polarised rewrite as a conditional rule *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred trigger }, f) } ->
    Some (Rewrite.Rule.mk
            ~guards:[Rewrite.Guard.Pred_true trigger]
            true (Rewrite.Trigger.Single trigger) (parse_result f))
  | { Expr.formula = Expr.Imply (
      { Expr.formula = Expr.Not { Expr.formula = Expr.Pred trigger } }, f) } ->
    Some (Rewrite.Rule.mk
            ~guards:[Rewrite.Guard.Pred_false trigger]
            true (Rewrite.Trigger.Single trigger) (parse_result f))

  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (cond, r) } ->
    CCOpt.map2 Rewrite.Rule.add_guards (parse_guards cond) (parse_manual_rule r)

  (* Not a rewrite rule, :p *)
  | _ -> None

let rec parse_rule_aux = function
  (* Equality&Equivalence as rewriting *)
  | { Expr.formula = Expr.Equal (a, b) }
  | { Expr.formula = Expr.Equiv (
          { Expr.formula = Expr.Pred a },
          { Expr.formula = Expr.Pred b })} ->
    begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt ->
        Some (Rewrite.Rule.mk false (Rewrite.Trigger.Single b) (Rewrite.Rule.Term a))
      | Comparison.Gt ->
        Some (Rewrite.Rule.mk false (Rewrite.Trigger.Single a) (Rewrite.Rule.Term b))
    end

  (* Polarised rewrite rule as conditional rewrite *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred p },
                                 { Expr.formula = Expr.Pred q })} ->
    begin match Lpo.compare p q with
      | Comparison.Gt ->
        Some (Rewrite.Rule.mk
                ~guards:[Rewrite.Guard.Pred_true p]
                false (Rewrite.Trigger.Single p) (Rewrite.Rule.Term q))
      | Comparison.Lt ->
        Some (Rewrite.Rule.mk
                ~guards:[Rewrite.Guard.Pred_false q]
                false (Rewrite.Trigger.Single q) (Rewrite.Rule.Term p))
      | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end

  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (cond, r) } ->
    CCOpt.map2 Rewrite.Rule.add_guards (parse_guards cond) (parse_rule_aux r)

  (* Other formulas are not rewrite rules *)
  | _ -> None


let parse_rule = function
  (* TODO: check that some variables are actually used in the rule ? *)
  | ({ Expr.formula = Expr.All (_, _, r) } as formula)
  | ({ Expr.formula = Expr.AllTy (_, _, {
         Expr.formula = Expr.All (_, _, r) })} as formula) ->
    let manual = CCOpt.is_some (Expr.Formula.get_tag formula Builtin.Tag.rwrt) in
    let parse = if manual then parse_manual_rule else parse_rule_aux in
    begin match parse r with
      | None ->
        if manual then
          Util.warn ~section
            "Following formula couldn't be parsed as a rewrite rule despite tag: %a"
            Expr.Print.formula r;
        None
      | Some rule ->
        Some (Rewrite.Rule.set_formula formula rule)
    end
  | _ -> None


(* Instantiate rewrite rules *)
(* ************************************************************************ *)

let insts = CCCache.unbounded 4013
    ~hash:(CCHash.pair Rewrite.Rule.hash Mapping.hash)
    ~eq:(CCEqual.pair Rewrite.Rule.equal Mapping.equal)

let instanciate rule subst =
  CCCache.with_cache insts (fun (rule, subst) ->
      Util.debug ~section "@[<hov 2>Instanciate %a@ with@ %a"
        (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
        rule Mapping.print subst;
      match rule.Rewrite.Rule.guards with
      | [] ->
        (* Instantiate the rule *)
        let clause, lemma = Inst.soft_subst rule.Rewrite.Rule.formula subst in
        Dispatcher.push clause lemma
      | guards ->
        let l = List.map (Rewrite.Guard.map (Mapping.apply_term subst)) guards in
        let watched = CCList.flat_map Rewrite.Guard.to_list l in
        (* Add a watch to instantiate the rule when the condition is true *)
        (* TODO: make sure the function is called only once *)
        Dispatcher.watch ~formula:rule.Rewrite.Rule.formula name 1 watched
          (fun () ->
             let l' = List.map (Rewrite.Guard.map Dispatcher.get_assign) l in
             if List.for_all Rewrite.Guard.check l' then begin
               let clause, lemma = Inst.soft_subst rule.Rewrite.Rule.formula subst in
               Dispatcher.push clause lemma
             end
          )
    ) (rule, subst)

let match_and_instantiate (rule, l) =
  Util.debug ~section:section_trigger "@[<hv 2>Matching rule %a:@ %a"
    Rewrite.Rule.print_id rule print_matching l;
  (** Trigger mode rewriting *)
  let seq = match_modulos l in
  List.iter (fun subst ->
      Util.debug ~section:section_trigger "match found:@ %a" Mapping.print subst;
      instanciate rule subst
    ) seq

(* Rewriter callbacks *)
(* ************************************************************************ *)

let rules_to_match s =
  CCList.flat_map (function
      | { Rewrite.Rule.trigger = Rewrite.Trigger.Single term; _ } as rule ->
        [rule, [term, T.elements s]]
      | { Rewrite.Rule.trigger = Rewrite.Trigger.Equal (t, t'); _ } as rule ->
        List.map (fun c ->
            rule, [t, [c];
                   t', T.elements @@ find_all_indexed @@ C.ty c]
          ) (T.elements s)
    ) !active_trigger_rules

(* Callback used when merging equivalence classes *)
let callback_merge a b t =
  Util.debug ~section "@[<hv 2>Eq class merge:@ @[<hov>%a@]@ @[<hov>%a@]@]"
    C.print a C.print b;
  let s = find_all_parents (C.repr t) in
  List.iter match_and_instantiate (rules_to_match s)

(* Callback used on new terms *)
let callback_term top t =
  Util.debug ~section "New term introduced: @[<hv>%a:@ %a@]"
    Expr.Print.term t Expr.Print.ty Expr.(t.t_type);
  (** Trigger rules *)
  let s = T.singleton (C.find t) in
  List.iter match_and_instantiate (rules_to_match s);
  (** Substitution rules *)
  if top then begin
    Util.debug ~section:section_subst "Tying to normalize@ %a" Expr.Print.term t;
    match Rewrite.Normalize.(normalize ~find:top_down !active_subst_rules t) with
    | [], t' ->
      assert (Expr.Term.equal t t');
      () (* nothing to do *)
    | rules, t' ->
      assert (not (Expr.Term.equal t t'));
      assert (Expr.Ty.equal Expr.(t.t_type) Expr.(t'.t_type));
      Util.info ~section:section_subst "@[<hv 2>Normalized term@ %a@ into@ %a@ using@ @[<hv>%a@]"
        Expr.Print.term t
        Expr.Print.term t'
        CCFormat.(list ~sep:(return "@ ") Rewrite.Rule.print) rules;
      let cond =
        List.map (fun r -> Expr.Formula.neg r.Rewrite.Rule.formula) rules
      in
      let lemma = Dispatcher.mk_proof name "subst" (Rewrite (Subst (t, rules))) in
      Dispatcher.push ((Expr.Formula.eq t t') :: cond) lemma
  end

(* Callback used on new rewrite rules *)
let callback_rule r kind =
  Util.debug ~section "New rule introduced";
  let aux = function
    (** A rewrite rule with a single var as trigger is impossile:
        wth a left side consisting of a single variable,
        what term on the right side of the rule could possibly be smaller ?
        on the other hand, it might be one part of a bigger trigger (such as (x = y)) *)
    | { Expr.term = Expr.Var _; t_type } -> T.elements @@ find_all_indexed t_type
    (** A trigger that consist of a single meta does not contain variable,
        thus has no reason to be a rewrite rule... *)
    | { Expr.term = Expr.Meta _ } -> assert false
    (** Rewrite rules trigger starts with an application, we can work with that. *)
    | { Expr.term = Expr.App (f, _, _) } -> T.elements @@ find_indexed f
  in
  match kind with
  | Trigger ->
    let l = match r.Rewrite.Rule.trigger with
      | Rewrite.Trigger.Single t -> [t, aux t]
      | Rewrite.Trigger.Equal (x, y) -> [x, aux x; y, aux y]
    in
    match_and_instantiate (r, l);
  | Substitution ->
    if not (index_is_empty ()) then
      Util.warn ~section:section_subst "%s,@ %s%s"
        "Adding rewrite rules while using subst mode"
        "this is not a supported use case, since it may change normale forms"
        "of already noramlized terms"

(* Rule addition callback *)
(* ************************************************************************ *)

(* When adding a new rule, we have to try and instantiate it. *)
let rec add_rule r =
  match !allow_mixed, current_mode (), Rewrite.Rule.is_manual r with
  | true, _, _
  | false, None, _
  | false, Some Manual, true
  | false, Some Auto, false ->
    let kind = split r in
    let () = match kind with
      | Substitution -> active_subst_rules := r :: !active_subst_rules
      | Trigger -> active_trigger_rules := r :: !active_trigger_rules
    in
    callback_rule r kind
  | false, Some Manual, false ->
    Util.warn ~section "Auto rule detected while in manual mode";
    Util.info ~section "@[<hv>Ignoring rule:@ %a@]"
      (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula) r;
    inactive_rules := r :: !inactive_rules
  | false, Some Auto, true ->
    Util.warn ~section "Detected manual rule while auto rules present";
    Util.info ~section "@[<hv>Keeping manual rules only:@ @[<v>%a@]@]"
      CCFormat.(list ~sep:(return "@ ") (
          Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
        ) !inactive_rules;
    Util.info ~section "@[<hv>Discarding auto rules:@ @[<v>%a@]@]"
      CCFormat.(list ~sep:(return "@ ") (
          Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
        ) (!active_subst_rules @ !active_trigger_rules);
    let l = !inactive_rules in
    inactive_rules := !active_trigger_rules @ !active_subst_rules;
    active_subst_rules := [];
    active_trigger_rules := [];
    List.iter add_rule l

(* Proof info *)
(* ************************************************************************ *)

let dot_info = function
  | Subst (t, l) ->
    Some "RED", (
      CCFormat.const Dot.Print.term t ::
      List.map (fun r ->
          CCFormat.const (
            Rewrite.Rule.print ~term:Dot.Print.term ~formula:Dot.Print.formula
          ) r
        ) l
    )

(* Plugin *)
(* ************************************************************************ *)

let assume f =
  (* Detect rewrite rules *)
  let () = match parse_rule f with
    | None ->
      Util.debug ~section "@[<hov 2>Failed to detect rewrite rule with:@ %a@]"
        Expr.Print.formula f;
    | Some r ->
      Expr.Formula.tag f tag true;
      Util.debug ~section "@[<hov 2>Detected a new rewrite rule:@ %a@]"
        (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula) r;
      add_rule r
  in
  ()

let rec peek = function
  | { Expr.formula = Expr.Pred p } ->
    register true p
  | { Expr.formula = Expr.Equal (a, b) } ->
    register true a;
    register true b
  | { Expr.formula = Expr.Not f } ->
    peek f
  | _ -> ()

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Rewrite info -> Some (dot_info info)
  | _ -> None

let options =
  let docs = Options.ext_sect in
  let aux b =
    allow_mixed := b;
    ()
  in
  let allow_mixed =
    let doc = "Allow mixed set of rewriting rules, i.e. allow automatically
               detected rules together with manually specified rules." in
    Cmdliner.Arg.(value & opt bool false & info ["rwrt.mixed"] ~docs ~doc)
  in
  Cmdliner.Term.(pure aux $ allow_mixed)

let register () =
  add_callback callback_term;
  Ext_eq.register_callback name callback_merge;
  Dispatcher.Plugin.register name ~options ~prio:20
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~peek ~assume ~section ~handle:{Dispatcher.handle} ())

