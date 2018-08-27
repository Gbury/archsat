(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Extension name *)
let name = "rwrt"

(* Module initialisation *)
(* ************************************************************************ *)

module C = Ext_eq.Class
module T = CCSet.Make(C)
module S = Set.Make(Expr.Term)

module H = Hashtbl.Make(Expr.Term)
module M = Hashtbl.Make(Expr.Id.Const)
module F = CCHashtbl.Make(Expr.Formula)

let section = Section.make ~parent:Dispatcher.section "rwrt"
let section_subst = Section.make ~parent:section "subst"
let section_narrow = Section.make ~parent:section "narrow"
let section_trigger = Section.make ~parent:section "trigger"

let tag = Tag.create ()
let normalized = Tag.create ()
let normal_form = Tag.create ()

type lemma_info = Subst of Expr.formula * Expr.formula * Rewrite.Subst.t list

type Dispatcher.lemma_info += Rewrite of lemma_info

(* Statistics *)
(* ************************************************************************ *)

let stats_static = Stats.mk "static"

let stats_norm = Stats.mk "rewrites"
let stats_steps = Stats.mk "steps"
let stats_eqmatch = Stats.mk "match modulo eq"
let stats_narrow = Stats.mk "narrow"

let static_group = Stats.bundle [
    stats_static;
    stats_norm;
    stats_steps;
    stats_eqmatch;
    stats_narrow;
  ]

let stats_dynamic = Stats.mk "dynamic"
let stats_triggered = Stats.mk "triggered"
let stats_applied = Stats.mk "applied"

let dynamic_group = Stats.bundle [
    stats_dynamic;
    stats_triggered;
    stats_applied;
  ]

let () = Stats.attach section static_group
let () = Stats.attach section dynamic_group

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

let mode_conv =
  let parse = function
    | "auto" -> Ok Auto
    | "manual" -> Ok Manual
    | s -> Error (`Msg (Format.sprintf "'%s' is not a recognized mode" s))
  in
  let print fmt = function
    | Auto -> Format.fprintf fmt "auto"
    | Manual -> Format.fprintf fmt "manual"
  in
  Cmdliner.Arg.conv (parse, print)

let forced_mode = ref None
let allow_mixed = ref false
let substitution_used = ref false

let current_mode () =
  match !forced_mode with
  | (Some _) as res -> res
  | None ->
    begin match !active_subst_rules, !active_trigger_rules with
      | [], [] -> None
      | r :: _, _
      | _, r :: _ ->
        Some (if Rewrite.Rule.is_manual r then Manual else Auto)
    end

let is_current_mode_forced () =
  match !forced_mode with
  | None -> false
  | Some _ -> true

let get_active () = !active_subst_rules @ !active_trigger_rules

(* Splitting rewrite rules *)
(* ************************************************************************ *)

type rule_type =
  | Trigger
  | Substitution

let split r =
  match Rewrite.Rule.(r.guards) with
  | [] ->
    begin match Dispatcher.get_absolute_truth Rewrite.Rule.(r.formula) with
      | Some true -> Substitution
      | Some false -> assert false
      | None -> Trigger
    end
  | _ -> Trigger

(* Callbacks on the set of known terms *)
(* ************************************************************************ *)

let add_callback, call =
  let r = ref [] in
  (fun f -> r := f :: !r),
  (fun top t -> List.iter (fun f -> f top t) !r)

(* Some printing functions *)
(* ************************************************************************ *)

let print_matching pat expr fmt (t, s) =
  Format.fprintf fmt "@[<hov>%a@ =?@[<hv>%a@]@]" pat t expr s

(* Registering parent-child relations between terms *)
(* ************************************************************************ *)

let checked = Tag.create ()
let parents = H.create 42
let index = M.create 42

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

let rec register_term top = function
  (* If the term has already been treated, nothing to do. *)
  | t when Expr.Term.get_tag t checked = Some () -> ()
  (* Else: *)
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    List.iter (add_parent t) l;
    add_to_index top f t;
    Expr.Term.tag t checked ();
    List.iter (register_term false) l

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

let iter_all_terms f =
  M.iter (fun _ s -> S.iter f s) index

let find_indexed_term f =
  let s = find_index f in
  S.fold (fun t acc -> T.add (C.find t) acc) s T.empty

let find_all_indexed_term ty =
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

(* Registering current set of formulas *)
(* ************************************************************************ *)

let pred_tbl = F.create 4013
let eqs_tbl = F.create 4013

let rec register_formula = function
  | { Expr.formula = Expr.Pred p } as f ->
    F.add pred_tbl f ();
    register_term true p
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    F.add eqs_tbl f ();
    register_term true a;
    register_term true b
  | { Expr.formula = Expr.Not f } -> register_formula f
  | _ -> ()

let find_indexed_eqs () = F.keys eqs_tbl
let find_indexed_pred () = F.keys pred_tbl
let find_indexed_negs () =
  Sequence.map Expr.Formula.neg @@
  Sequence.append (find_indexed_eqs ()) (find_indexed_pred ())

(* Matching modulo equivalence classes *)
(* ************************************************************************ *)

type mmatch = {
  eq_used : bool;       (* is an equality used for the match ? *)
  subst   : Mapping.t;  (* the mapping to use *)
}

let add_used b { subst; eq_used; } = { subst; eq_used = b || eq_used; }

let match_types pats args { eq_used; subst; } =
  try Some { eq_used; subst = List.fold_left2 Match.ty subst pats args; }
  with Match.Impossible_ty _ -> None

let match_modulo_var v c ({ eq_used; subst; } as m) =
  match Mapping.Var.get_term_opt subst v with
  | None ->
    begin try
        let tmp = Match.ty subst Expr.(v.id_type) Expr.(c.t_type) in
        Some { eq_used; subst = Mapping.Var.bind_term tmp v c; }
      with Match.Impossible_ty _ ->
        None
    end
  | Some d ->
    if Expr.Term.equal c d then
      Some m
    else
      None

let rec match_modulo_app f acc (ty_pats, pats) = function
  | { Expr.term = Expr.App (f', ty_args, args) } ->
    assert (Expr.Id.equal f f');
    let acc' = CCList.filter_map (match_types ty_pats ty_args) acc in
    let l = List.map C.find args in
    List.fold_left2 match_modulo_term acc' pats l
  | _ -> assert false

and match_modulo_term acc pat c =
  match pat with
  | { Expr.term = Expr.Var v } ->
    CCList.filter_map (match_modulo_var v (C.repr c)) acc
  | { Expr.term = Expr.Meta _ } as t ->
    if C.mem c t then acc else []
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let r = C.repr c in
    let l = C.find_top c f in
    CCList.flat_map (fun t ->
        List.map (add_used (Expr.Term.equal r t))
          (match_modulo_app f acc (ty_pats, pats) t)
      ) l

let rec match_modulo_formula acc pat f =
  match pat, f with
  | { Expr.formula = Expr.Pred p },
    { Expr.formula = Expr.Pred p' } ->
    match_modulo_term acc p (C.find p')
  | { Expr.formula = Expr.Equal (a, b) },
    { Expr.formula = Expr.Equal (c, d) } ->
    match_modulo_term (match_modulo_term acc a (C.find c)) b (C.find d) @
    match_modulo_term (match_modulo_term acc a (C.find d)) b (C.find c)
  | { Expr.formula = Expr.Not pat' },
    { Expr.formula = Expr.Not f' } -> match_modulo_formula acc pat' f'
  | _ -> []

let match_modulo_t = match_modulo_term [{ eq_used = false; subst = Mapping.empty; }]
let match_modulo_f = match_modulo_formula [{eq_used = false; subst = Mapping.empty; }]

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
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } ->
    Some (Rewrite.Guard.Neq (a, b))
  | _ -> None

let parse_guards = function
  | { Expr.formula = Expr.And l } ->
    CCOpt.sequence_l (List.map parse_guard l)
  | f ->
    CCOpt.map (fun x -> [x]) (parse_guard f)

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
    Some Rewrite.(Rule.mk_term true trigger result)
  | { Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Equal _ } as trigger, result) } ->
    Some Rewrite.(Rule.mk_formula true trigger result)
  | { Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Pred trigger },
                                 { Expr.formula = Expr.Pred result } ) } ->
    Some (Rewrite.Rule.mk_term true trigger result)
  | { Expr.formula = Expr.Equiv (trigger, result) } ->
    Some (Rewrite.Rule.mk_formula true trigger result)

  (* Polarised rewrite as a conditional rule *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred trigger },
                                 { Expr.formula = Expr.Pred result } ) } ->
    Some (Rewrite.Rule.mk_term true trigger result
            ~guards:[Rewrite.Guard.Pred_true trigger])
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred guard } as trigger, result) } ->
    Some (Rewrite.Rule.mk_formula true trigger result
            ~guards:[Rewrite.Guard.Pred_true guard])
  | { Expr.formula = Expr.Imply (
      { Expr.formula = Expr.Not { Expr.formula = Expr.Pred trigger } },
      { Expr.formula = Expr.Pred result } ) } ->
    Some (Rewrite.Rule.mk_term true trigger result
            ~guards:[Rewrite.Guard.Pred_false trigger])
  | { Expr.formula = Expr.Imply (
      { Expr.formula = Expr.Not ({ Expr.formula = Expr.Pred guard } as trigger) }, result) } ->
    Some (Rewrite.Rule.mk_formula true trigger result
            ~guards:[Rewrite.Guard.Pred_false guard])

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
      | Comparison.Lt -> Some (Rewrite.Rule.mk_term false b a)
      | Comparison.Gt -> Some (Rewrite.Rule.mk_term false a b)
    end

  (* Polarised rewrite rule as conditional rewrite *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred p },
                                 { Expr.formula = Expr.Pred q })} ->
    begin match Lpo.compare p q with
      | Comparison.Eq
      | Comparison.Incomparable -> None
      | Comparison.Gt -> Some (Rewrite.Rule.mk_term false p q
                                 ~guards:[Rewrite.Guard.Pred_true p])
      | Comparison.Lt -> Some (Rewrite.Rule.mk_term false q p
                                 ~guards:[Rewrite.Guard.Pred_false q])
    end

  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (cond, r) } ->
    CCOpt.map2 Rewrite.Rule.add_guards (parse_guards cond) (parse_rule_aux r)

  (* Other formulas are not rewrite rules *)
  | _ -> None


let parse_rule = function
  (* TODO: check that some variables are actually used in the rule ? *)
  | ({ Expr.formula = Expr.All (_, _, r) } as formula) ->
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

(** Substs should be enough to ensure unicity of rewrites, since
    variables for different rewrite rules should be different. *)
let watch =
  Dispatcher.mk_watch (module Mapping) name

let insts = CCCache.unbounded 4013
    ~hash:(CCHash.pair Rewrite.Rule.hash Mapping.hash)
    ~eq:(CCEqual.pair Rewrite.Rule.equal Mapping.equal)

let instanciate rule subst =
  CCCache.with_cache insts (fun (rule, subst) ->
      Stats.incr stats_triggered section;
      Util.debug ~section "@[<hov 2>Instanciate %a@ with@ %a"
        (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
        rule Mapping.print subst;
      match rule.Rewrite.Rule.guards with
      | [] ->
        (* Instantiate the rule *)
        let clause, lemma =
          Inst.soft_subst ~name:"trigger" rule.Rewrite.Rule.formula subst in
        Dispatcher.push clause lemma
      | guards ->
        let l = List.map (Rewrite.Guard.map (Mapping.apply_term subst)) guards in
        let watched =
          CCList.sort_uniq ~cmp:Expr.Term.compare @@
          CCList.flat_map Rewrite.Guard.to_list l
        in
        (* Add a watch to instantiate the rule when the condition is true *)
        (* TODO: make sure the function is called only once *)
        watch ~formula:rule.Rewrite.Rule.formula subst 1 watched
          (fun () ->
             let l' = List.map (Rewrite.Guard.map Dispatcher.get_assign) l in
             try
               let g = List.find (fun g -> not (Rewrite.Guard.check g)) l' in
               Util.debug ~section "False condition:@ %a"
                 (Rewrite.Guard.print ~term:Expr.Term.print) g
             with Not_found ->
               Stats.incr stats_applied section;
               Util.debug ~section "All conditions true, pushing rewrite";
               let clause, lemma =
                 Inst.soft_subst ~name:"trigger" rule.Rewrite.Rule.formula subst in
               Dispatcher.push clause lemma
          )
    ) (rule, subst)

let match_and_instantiate ~pat ~expr ~only_eq ~match_fun (rule, t, c) =
  Util.debug ~section:section_trigger "@[<hv 2>Matching rule %a:@ %a"
    Rewrite.Rule.print_id rule (print_matching pat expr) (t, c);
  (** Trigger mode rewriting *)
  let seq = match_fun t c in
  List.iter (fun { eq_used; subst; } ->
      Util.debug ~section:section_trigger "match found:@ %a" Mapping.print subst;
      if only_eq && not eq_used then
        Util.debug ~section "Ignoring match because no equality was used to match"
      else begin
        Stats.incr stats_eqmatch section;
        instanciate rule subst
      end
    ) seq

let match_and_instantiate_term =
  match_and_instantiate ~pat:Expr.Print.term ~expr:C.print

let match_and_instantiate_formula =
  match_and_instantiate ~pat:Expr.Print.formula ~expr:Expr.Print.formula

(* Rewriter callbacks *)
(* ************************************************************************ *)

let rules_to_match s =
  let l = T.elements s in
  CCList.flat_map (function
      | Rewrite.Rule.{ contents = C (Formula, _ ) } as rule ->
        Util.warn ~section:section_trigger "Formula-matching not supported in trigger rules";
        Util.info ~section:section_trigger
          "@[<hv 2>Following rule wasn't used for matching:@ %a@]"
          (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula) rule;
        ([] : (Rewrite.Rule.t * Expr.term * C.t) list)
      | Rewrite.Rule.{ contents = C (Term, { trigger; _ }) } as rule ->
        ((List.map (fun x -> rule, trigger, x) l) : (Rewrite.Rule.t * Expr.term * C.t) list)
    ) !active_trigger_rules

(* Callback used when merging equivalence classes *)
let callback_merge a b t =
  Util.debug ~section "@[<hv 2>Eq class merge:@ @[<hov>%a@]@ @[<hov>%a@]@]"
    C.print a C.print b;
  let s = find_all_parents (C.repr t) in
  List.iter (match_and_instantiate_term
               ~only_eq:false ~match_fun:match_modulo_t) (rules_to_match s)

(* Callback used on new terms *)
let callback_term top t =
  Util.debug ~section "New term introduced: @[<hv>%a:@ %a@]"
    Expr.Print.term t Expr.Print.ty Expr.(t.t_type);
  (** Trigger rules *)
  let s = T.singleton (C.find t) in
  List.iter (match_and_instantiate_term
               ~only_eq:false ~match_fun:match_modulo_t) (rules_to_match s)

(* Find all potential term classes to match against a rewrite rule *)
let potential_term_matches = function
  (** A rewrite rule with a single var as trigger is impossile:
      with a left side consisting of a single variable,
      what term on the right side of the rule could possibly be smaller ?
      on the other hand, it might be one part of a bigger trigger (such as (x = y)) *)
  | { Expr.term = Expr.Var _; t_type } -> T.elements @@ find_all_indexed_term t_type
  (** A trigger that consist of a single meta does not contain variable,
      thus has no reason to be a rewrite rule... *)
  | { Expr.term = Expr.Meta _ } -> assert false
  (** Rewrite rules trigger starts with an application, we can work with that. *)
  | { Expr.term = Expr.App (f, _, _) } -> T.elements @@ find_indexed_term f

(* Find all potential formulas to match against a rewrite rule *)
let potential_formula_matches = function
  | { Expr.formula = Expr.Pred _ } -> find_indexed_pred ()
  | { Expr.formula = Expr.Equal _ } -> find_indexed_eqs ()
  (** Formula triggers should be atomic, hence if it starts with a
      negation, it should be of the form (Neg Pred) or (Neg Equal) *)
  | { Expr.formula = Expr.Not ({
      Expr.formula = (Expr.Pred _ | Expr.Equal _ ) }
    ) } -> find_indexed_negs ()
  | _ -> assert false

(* Callback used on new rewrite rules *)
let callback_rule r kind =
  Util.debug ~section "New rule introduced";
  match kind with
  | Trigger ->
    begin match r.Rewrite.Rule.contents with
      | Rewrite.Rule.(C (Term, { trigger; _ })) ->
        List.iter (fun c ->
            match_and_instantiate_term
              ~only_eq:false ~match_fun:match_modulo_t (r, trigger, c)
          ) (potential_term_matches trigger)
      | Rewrite.Rule.(C (Formula, {trigger; _ })) ->
        Sequence.iter (fun c ->
            match_and_instantiate_formula
              ~only_eq:false ~match_fun:match_modulo_f (r, trigger, c)
          ) (potential_formula_matches trigger)
    end
  | Substitution ->
    if !substitution_used then
      Util.warn ~section:section_subst "@[<hov>%a@]" CCFormat.text
        ("Adding a substitution rewrite rule after a term has" ^
         "already been rewritten. This is not a supported use case," ^
         "since it may change normal forms of already noramlized terms")

let substitute f =
  (** Substitution rules *)
  Util.debug ~section:section_subst "Trying to normalize@ %a" Expr.Print.formula f;
  match Rewrite.Normalize.(normalize_atomic !active_subst_rules [] f) with
  | f', [] ->
    assert (Expr.Formula.equal f f');
    Expr.Formula.tag f normal_form true; (* already in normal form, nothing to do *)
  | f', substs ->
    assert (not (Expr.Formula.equal f f'));
    assert (not (Expr.Formula.get_tag f normal_form = Some true));
    Stats.incr stats_norm section;
    Stats.incr stats_steps section ~k:(List.length substs);
    substitution_used := true;
    Expr.Formula.tag f' normal_form true;
    Util.debug ~section:section_subst "@[<hv 2>Normalized term@ %a@ into@ %a@ using@ @[<hv>%a@]"
      Expr.Print.formula f
      Expr.Print.formula f'
      CCFormat.(list ~sep:(return "@ ") Rewrite.Subst.print) substs;
    let cond =
      List.map (fun s ->
          Expr.Formula.neg (Rewrite.Subst.rule s).Rewrite.Rule.formula
        ) substs
    in
    let lemma = Dispatcher.mk_proof name "subst" (Rewrite (Subst (f, f', substs))) in
    Dispatcher.push ((Expr.Formula.equiv f f') :: cond) lemma

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
      | Substitution ->
        Stats.incr stats_static section;
        active_subst_rules := r :: !active_subst_rules
      | Trigger ->
        Stats.incr stats_dynamic section;
        active_trigger_rules := r :: !active_trigger_rules
    in
    Expr.Formula.tag r.Rewrite.Rule.formula tag true;
    callback_rule r kind
  | false, Some Manual, false ->
    (if is_current_mode_forced () then Util.info else Util.warn)
      ~section "Auto rule detected while in manual mode";
    Util.info ~section "@[<hv>Ignoring rule:@ %a@]"
      (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula) r;
    inactive_rules := r :: !inactive_rules
  | false, Some Auto, true ->
    if is_current_mode_forced () then begin
      Util.error ~section "@[<hov>%s,@ %s@]"
        "Manual rule detected while in forced auto mode"
        "please check that everything is as should be...";
    end else begin
      (* TODO: this is incomplete as auto rules were prohibited from generating meta variables *)
      Util.warn ~section "@[<hov>%s,@ %s,@ %s@]"
        "Detected manual rule while auto rules present"
        "removing auto rules and replacing them with manual rules"
        "consider forcing manual mode using options";
      Util.info ~section "@[<hv>Keeping manual rules only:@ @[<v>%a@]@]"
        CCFormat.(list ~sep:(return "@ ") (
            Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
          ) !inactive_rules;
      Util.info ~section "@[<hv>Discarding auto rules:@ @[<v>%a@]@]"
        CCFormat.(list ~sep:(return "@ ") (
            Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula)
          ) (!active_subst_rules @ !active_trigger_rules);
      let l = !inactive_rules in
      Stats.set stats_static section 0;
      Stats.set stats_dynamic section 0;
      inactive_rules := !active_trigger_rules @ !active_subst_rules;
      active_subst_rules := [];
      active_trigger_rules := [];
      List.iter add_rule l
    end

(* Narrowing *)
(* ************************************************************************ *)

let do_narrowing () =
  let ret = ref false in
  let rules = !active_trigger_rules @ !active_subst_rules in
  iter_all_terms (fun t ->
      let l = Rewrite.Narrow.term t rules in
      let l = List.map (fun (_, _, m) -> m) l in
      List.iter (fun m ->
          Util.debug ~section:section_narrow
            "@[<hv 2>Found a unifier:@ %a@]" Mapping.print m;
          List.iter (fun m ->
              let b = Inst.add ~name:"narrowing" m in
              if b then Stats.incr stats_narrow section;
              ret := b || !ret
            ) (Inst.partition @@ Inst.generalize m)
        ) l
    );
  !ret

(* Proof info *)
(* ************************************************************************ *)

let dot_info = function
  | Subst (f, f', l) ->
    Some "PURPLE", (
      CCFormat.const Dot.Print.formula f ::
      CCFormat.const Dot.Print.formula f' ::
      List.map (fun r ->
          CCFormat.const (
            Rewrite.Rule.print ~term:Dot.Print.term ~formula:Dot.Print.formula
          ) (Rewrite.Subst.rule r)
        ) l
    )

let proof_inst s pos =
  pos
  |> Inst.proof (Rewrite.Subst.formula s) (Rewrite.Subst.inst s)
  |> Logic.ensure Logic.trivial

let proof_inst_not s pos =
  pos |> Logic.equiv_not |> proof_inst s

let rec proof_chain goal l pos =
  match l with
  | [] -> pos
  | s :: r ->
    Util.debug ~section "@[<hv 2>current rewrite goal:@ %a@]" Term.print goal;
    begin match Rewrite.Subst.info s with
      | Rewrite.Rule.C (Rewrite.Rule.Term, { Rewrite.Rule.trigger; result }) ->
        if Expr.Ty.equal Expr.Ty.prop Expr.(trigger.t_type) then begin
          proof_prop goal r s (Expr.Formula.pred trigger) (Expr.Formula.pred result) pos
        end else
          proof_term goal r s (trigger : Expr.term) (result : Expr.term) pos
      | Rewrite.Rule.C (Rewrite.Rule.Formula, { Rewrite.Rule.trigger; result }) ->
        proof_prop goal r s (trigger : Expr.formula) (result : Expr.formula) pos
    end

and proof_term goal r s trigger result pos =
  let trigger_t = Term.of_term trigger in
  let result_t = Term.of_term result in
  match Position.Proof.find trigger_t goal with
  | Some p ->
    pos
    |> Eq.subst p goal ~by:result_t ~eq:(proof_inst s)
    |> proof_chain (CCOpt.get_exn @@ Position.Proof.substitute p ~by:result_t goal) r
  | None ->
    raise (Proof.Failure ("Ext_rewrite.proof_chain", pos))

and proof_prop goal r s trigger result pos =
  Util.debug ~section "@[<hv>chaining (prop):@ r: %a@ m: %a@ triger: %a@ result: %a@]"
    Expr.Formula.print (Rewrite.Subst.formula s)
    Mapping.print (Rewrite.Subst.inst s)
    Expr.Formula.print trigger
    Expr.Formula.print result;
  let trigger_t = Term.of_formula trigger in
  let result_t = Term.of_formula result in
  Util.debug ~section "@[<v>trigger_t: %a@ result_t: %a@]"
    Term.print trigger_t Term.print result_t;
  let (left, right) = CCOpt.get_exn @@ Logic.match_equiv goal in
  begin match Position.Proof.find trigger_t goal with
    | Some p ->
      if Term.Reduced.equal left trigger_t ||
         Term.Reduced.equal right trigger_t then begin
        pos
        |> Logic.equiv_replace trigger_t ~by:result_t ~equiv:(proof_inst s)
        |> proof_chain (CCOpt.get_exn @@ Position.Proof.substitute p ~by:result_t goal) r
      end else begin
        pos
        |> Logic.equiv_replace
          (Term.app Term.not_term trigger_t)
          ~by:(Term.app Term.not_term result_t)
          ~equiv:(proof_inst_not s)
        |> proof_chain (CCOpt.get_exn @@ Position.Proof.substitute p ~by:result_t goal) r
      end
    | None ->
      Util.error ~section "@[<hv>Position not found for@ %a@ in@ %a@]"
        Term.print trigger_t Term.print goal;
      raise (Proof.Failure ("Ext_rewrite.proof_chain", pos))
  end

let coq_proof = function
  | Subst (f, f', l) ->
    Util.debug ~section "@[<hv>Normalized@ %a@ into@ %a@]"
      Expr.Formula.print f Expr.Formula.print f';
    (fun pos ->
       pos
       |> Logic.introN "Q" (List.length l + 1)
       |> Logic.fold (fun s ->
           Logic.not_not_elim "Q" (Term.of_formula (Rewrite.Subst.formula s))) l
       |> Logic.find (Term.app Term.not_term @@ Term.of_formula (Expr.Formula.equiv f f'))
         (Logic.apply1 [])
       |> proof_chain (Term.of_formula (Expr.Formula.equiv f f')) l
       |> Logic.equiv_refl (Term.of_formula f')
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
      Util.debug ~section "@[<hov 2>Detected a new rewrite rule:@ %a@]"
        (Rewrite.Rule.print ~term:Expr.Print.term ~formula:Expr.Print.formula) r;
      add_rule r
  in
  (* Apply substitution rules *)
  let () =
    match Expr.Formula.get_tag f normalized with
    | Some true -> ()
    | None | Some false ->
      let () = substitute f in
      Expr.Formula.tag f normalized true
  in
  ()

let set_watcher = register_formula

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Rewrite info -> Some (dot_info info)
  | Proof.Lemma Rewrite info -> Some (coq_proof info)
  | Solver.Found_sat _ ->
    if do_narrowing () then Some (Solver.Assume []) else Some Solver.Sat_ok
  | _ -> None

let options =
  let docs = Options.ext_sect in
  let aux mixed forced =
    allow_mixed := mixed;
    forced_mode := forced;
    ()
  in
  let allow_mixed =
    let doc = "Allow mixed set of rewriting rules, i.e. allow automatically
               detected rules together with manually specified rules." in
    Cmdliner.Arg.(value & opt bool false & info ["rwrt.mixed"] ~docs ~doc)
  in
  let forced_mode =
    let doc = {|Force mode for detecting rewrite rules. Manual rules are
                annotated formulas (for instance, "rewrite statements in
                zipperposition format"), while auto rules are formulas detected
                as potentially oriented rewrite rules using internal heuristics.|} in
    Cmdliner.Arg.(value & opt (some mode_conv) None & info ["rwrt.mode"] ~docs~doc)
  in
  Cmdliner.Term.(pure aux $ allow_mixed $ forced_mode)

let register () =
  add_callback callback_term;
  Ext_eq.register_callback name callback_merge;
  Dispatcher.Plugin.register name ~options ~prio:20
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~set_watcher ~assume ~section ~handle:{Dispatcher.handle} ())

