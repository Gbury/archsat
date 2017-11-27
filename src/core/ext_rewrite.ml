
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
let tag = Tag.create ()

(* Callbacks on the set of known terms *)
(* ************************************************************************ *)

let add_callback, call =
  let r = ref [] in
  (function f -> r := f :: !r),
  (function t -> List.iter ((|>) t) !r)

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

let add_to_index f t =
  call t;
  let s = find_index f in
  M.replace index f (S.add t s)

let rec register = function
  (* If the term has already been treated, nothing to do. *)
  | t when Expr.Term.get_tag t checked = Some () -> ()
  (* Else: *)
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    List.iter (add_parent t) l;
    add_to_index f t;
    Expr.Term.tag t checked ();
    List.iter register l

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

(* Rewrite rules guards *)
(* ************************************************************************ *)

type guard =
  | Pred of Expr.term
  | Eq of Expr.term * Expr.term

let print_guard ?(term=Expr.Print.term) fmt = function
  | Pred p ->
    Format.fprintf fmt "%a" term p
  | Eq (a, b) ->
    Format.fprintf fmt "%a=%a" term a term b

let map_guard f = function
  | Pred p -> Pred (f p)
  | Eq (a, b) -> Eq (f a, f b)

let guard_to_list = function
  | Pred p -> [p]
  | Eq (a, b) -> [a; b]

let guard_to_formula = function
  | Pred p -> Expr.Formula.pred p
  | Eq (a, b) -> Expr.Formula.eq a b

let check_guard = function
  | Pred p -> Expr.Term.equal p Builtin.Misc.p_true
  | Eq (a, b) -> Expr.Term.equal a b

(* Rewrite rules triggers *)
(* ************************************************************************ *)

type 'a trigger =
  | Single of 'a
  | Equal of 'a * 'a

let trigger_map f = function
  | Single x -> Single (f x)
  | Equal (x, y) -> Equal (f x, f y)

let print_trigger pp fmt = function
  | Single x -> pp fmt x
  | Equal (x, y) -> Format.fprintf fmt "%a ==@ %a" pp x pp y

(* Rewrite rules definition *)
(* ************************************************************************ *)

type 'a rule = {
  id       : int;
  manual   : bool;
  trigger  : 'a trigger;
  guards   : guard list;
  formula  : Expr.formula;
}

let _nb_rules = ref 0

let mk ?(guards=[]) manual trigger formula =
  let () = incr _nb_rules in
  { id = !_nb_rules; manual; trigger; guards; formula; }

let map_trigger f rule =
  { rule with trigger = f rule.trigger }

let add_guards guards rule =
  { rule with guards = guards @ rule.guards }

let set_formula formula rule = { rule with formula }

let is_manual { manual; } = manual

let rec print_guards ?term fmt = function
  | [] -> ()
  | g :: r ->
    Format.fprintf fmt "@[<hov>[%a]@,%a@]"
      (print_guard ?term) g (print_guards ?term) r

let print_rule_id fmt r =
  Format.fprintf fmt "%s%d" (if r.manual then "~" else "#") r.id

let print_rule
    ?(term=Expr.Print.term) pp
    fmt ({ trigger; guards; _ } as r) =
  Format.fprintf fmt "@[<hov 2>%a%a@ %a@]"
    print_rule_id r
    (print_guards ~term) guards
    (print_trigger pp) trigger

let print_matching_aux fmt (t, s) =
  Format.fprintf fmt "@[<hov>%a@ =?@[<hv>%a@]@]"
    Expr.Print.term t CCFormat.(list ~sep:(return ",@ ") C.print) s

let print_matching fmt l =
  Format.fprintf fmt "@[<hv>%a@]"
    CCFormat.(list ~sep:(return ";@ ") print_matching_aux) l

(* Plugin state *)
(* ************************************************************************ *)

let active_rules = ref []
let inactive_rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack active_rules
let () = Backtrack.Stack.attach Dispatcher.stack inactive_rules

type mode =
  | Auto
  | Manual

let current_mode () =
  match !active_rules with
  | [] -> None
  | r :: _ -> Some (if is_manual r then Manual else Auto)

let allow_mixed = ref false

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

(* Parse an arbitrary formula as a rewrite rule *)
let parse_guard = function
  | { Expr.formula = Expr.Pred p } -> Some (Pred p)
  | { Expr.formula = Expr.Equal (a, b) } -> Some (Eq (a, b))
  | _ -> None

let parse_guards = function
  | { Expr.formula = Expr.And l } ->
    CCOpt.sequence_l (List.map parse_guard l)
  | f ->
    CCOpt.map (fun x -> [x]) (parse_guard f)

(* Parse manually oriented rules *)
let parse_manual_rule = function
  (* Standard rewrite rules *)
  | ({ Expr.formula = Expr.Equal (a, b) } as f) ->
    let trigger =
      match Expr.Formula.get_tag f Expr.t_order with
      | None -> assert false
      | Some Expr.Same -> a
      | Some Expr.Inverse -> b
    in
    Some (mk true (Single trigger) f)
  | ({ Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Equal (a, b) }, _) } as f) ->
    Some (mk true (Equal (a, b)) f)
  | ({ Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Pred trigger }, _) } as f) ->
    Some (mk true (Single trigger) f)

  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (
      cond,
      (* Rewrite rule *)
      (({ Expr.formula = Expr.Equal (trigger, _) } as f)
      |({ Expr.formula = Expr.Equiv (
            { Expr.formula = Expr.Pred trigger }, _) } as f)))} ->
    CCOpt.map (fun guards -> mk ~guards true (Single trigger) f) (parse_guards cond)

  (* Polarised rewrite as a conditional rule *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred trigger }, f) } ->
    Some (mk ~guards:[Pred trigger] true (Single trigger) f)

  (* Not a rewrite rule, :p *)
  | _ -> None

let rec parse_rule_aux = function
  (* Equality&Equivalence as rewriting *)
  | ({ Expr.formula = Expr.Equal (a, b) } as f)
  | ({ Expr.formula = Expr.Equiv (
         { Expr.formula = Expr.Pred a },
         { Expr.formula = Expr.Pred b })} as f) ->
    begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt -> Some (mk false (Single b) f)
      | Comparison.Gt -> Some (mk false (Single a) f)
    end

  (* Polarised rewrite rule as conditional rewrite *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred trigger },
                                 ({ Expr.formula = Expr.Pred p } as f))} ->
    begin match Lpo.compare trigger p with
      | Comparison.Gt -> Some (mk false (Single trigger) f)
      | Comparison.Lt | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end

  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (cond, r) } ->
    CCOpt.map2 add_guards (parse_guards cond) (parse_rule_aux r)

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
        Expr.Formula.tag formula tag true;
        Some (set_formula formula rule)
    end
  | _ -> None

(* Rewrite proofs *)
(* ************************************************************************ *)

type lemma_info = Inst of Expr.term rule * Mapping.t

type Dispatcher.lemma_info += Rewrite of lemma_info

(* Instantiate rewrite rules *)
(* ************************************************************************ *)

let instanciate rule subst =
  let pp fmt t = Expr.Print.term fmt t in
  Util.debug ~section "@[<hov 2>Instanciate %a@ with@ %a"
    (print_rule pp) rule Mapping.print subst;
  match rule.guards with
  | [] ->
    (* Instantiate the rule *)
    let clause, lemma = Inst.soft_subst rule.formula subst in
    Dispatcher.push clause lemma
  | guards ->
    let l = List.map (map_guard (Mapping.apply_term subst)) guards in
    let watched = CCList.flat_map guard_to_list l in
    (* Add a watch to instantiate the rule when the condition is true *)
    (* TODO: make sure the function is called only once *)
    Dispatcher.watch ~formula:rule.formula name 1 watched
      (fun () ->
         let l' = List.map (map_guard Dispatcher.get_assign) l in
         if List.for_all check_guard l' then begin
           let clause, lemma = Inst.soft_subst rule.formula subst in
           Dispatcher.push clause lemma
         end
      )

let match_and_instantiate (rule, l) =
  Util.debug ~section "@[<hv 2>Matching rule %a:@ %a"
    print_rule_id rule print_matching l;
  let seq = match_modulos l in
  List.iter (fun subst ->
      Util.debug ~section "match found:@ %a" Mapping.print subst;
      instanciate rule subst
    ) seq

(* Rewriter callbacks *)
(* ************************************************************************ *)

let rules_to_match s =
  CCList.flat_map (function
      | { trigger = Single term; _ } as rule ->
        [rule, [term, T.elements s]]
      | { trigger = Equal (t, t'); _ } as rule ->
        List.map (fun c ->
            rule, [t, [c];
                   t', T.elements @@ find_all_indexed @@ C.ty c]
          ) (T.elements s)
    ) !active_rules

(* Callback used when merging equivalence classes *)
let callback_merge a b t =
  Util.debug ~section "@[<hv 2>Eq class merge:@ @[<hov>%a@]@ @[<hov>%a@]@]"
    C.print a C.print b;
  let s = find_all_parents (C.repr t) in
  List.iter match_and_instantiate (rules_to_match s)

(* Callback used on new terms *)
let callback_term t =
  Util.debug ~section "New term introduced: @[<hv>%a:@ %a@]"
    Expr.Print.term t Expr.Print.ty Expr.(t.t_type);
  let s = T.singleton (C.find t) in
  List.iter match_and_instantiate (rules_to_match s)

(* Callback used on new rewrite rules *)
let callback_rule r =
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
  let l = match r.trigger with
    | Single t -> [t, aux t]
    | Equal (x, y) -> [x, aux x; y, aux y]
  in
  match_and_instantiate (r, l)

(* Rule addition callback *)
(* ************************************************************************ *)

(* When adding a new rule, we have to try and instantiate it. *)
let add_rule r =
  match !allow_mixed, current_mode (), is_manual r with
  | true, _, _
  | false, None, _
  | false, Some Manual, true
  | false, Some Auto, false ->
    active_rules := r :: !active_rules;
    callback_rule r
  | false, Some Manual, false ->
    Util.warn ~section "Auto rule detected while in manual mode";
    Util.info ~section "@[<hv>Ignoring rule:@ %a@]" (print_rule Expr.Print.term) r;
    inactive_rules := r :: !inactive_rules
  | false, Some Auto, true ->
    Util.warn ~section "Detected manual rule while auto rules present";
    Util.info ~section "@[<hv>Keeping manual rules only:@ @[<v>%a@]@]"
      CCFormat.(list ~sep:(return "@ ") (print_rule Expr.Print.term)) !inactive_rules;
    Util.info ~section "@[<hv>Discarding auto rules:@ @[<v>%a@]@]"
      CCFormat.(list ~sep:(return "@ ") (print_rule Expr.Print.term)) !active_rules;
    let l = !inactive_rules in
    inactive_rules := !active_rules;
    active_rules := l

(* Proof info *)
(* ************************************************************************ *)

let dot_info = function
  | Inst (r, s) ->
    Some "RED", [
      CCFormat.const Dot.Print.mapping s;
      CCFormat.const (
        print_rule
          ~term:Dot.Print.term
          Dot.Print.term) r;
    ]

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
        (print_rule Expr.Print.term) r;
      add_rule r
  in
  ()

let rec peek = function
  | { Expr.formula = Expr.Pred p } ->
    register p
  | { Expr.formula = Expr.Equal (a, b) } ->
    register a;
    register b
  | { Expr.formula = Expr.Not f } ->
    peek f
  | _ -> ()

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Rewrite info -> Some (dot_info info)
  | _ -> None

let options =
  let docs = Options.ext_sect in
  let aux b =
    allow_mixed := b
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
  Dispatcher.Plugin.register name ~options
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~peek ~assume ~section ~handle:{Dispatcher.handle} ())

