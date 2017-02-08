
(* Extension name *)
let name = "rwrt"

(* Module initialisation *)
(* ************************************************************************ *)

module C = Ext_eq.Class
module T = Set.Make(C)
module S = Set.Make(Expr.Term)

module H = Hashtbl.Make(Expr.Term)
(* TODO: Name the struct to avoid duplicating code (see ext_eq) *)
module M = Hashtbl.Make(struct
    type t = Expr.ty Expr.function_descr Expr.id
    let hash = Expr.Id.hash
    let equal = Expr.Id.equal
  end)

let section = Util.Section.make ~parent:Dispatcher.section "rwrt"

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


(* Matching modulo equivalence classes *)
(* ************************************************************************ *)

let match_types pats args subst =
  try Some (List.fold_left2 Match.ty subst args pats)
  with
  | Match.Impossible_ty _ -> None
  | Match.Impossible_term _ -> assert false

let match_modulo_var v c subst =
  match Match.get_term_opt subst v with
  | None ->
    Some (Match.bind_term subst v c)
  | Some d ->
    if Expr.Term.equal c d then
      Some subst
    else
      None

let rec match_modulo_app acc (ty_pats, pats) = function
  | { Expr.term = Expr.App (_, ty_args, args) } ->
    let acc' = CCList.filter_map (match_types ty_pats ty_args) acc in
    Util.debug ~section 50 "     + type matching: %d results" (List.length acc');
    let l = List.map C.find args in
    List.fold_left2 match_modulo_aux acc' pats l
  | _ -> assert false

and match_modulo_aux acc pat c =
  Util.debug ~section 50 " - matching %a <--> %a"
    Expr.Term.debug pat C.debug c;
  match pat with
  | { Expr.term = Expr.Var v } ->
    Util.debug ~section 50 "   > variable";
    CCList.filter_map (match_modulo_var v (C.repr c)) acc
  | { Expr.term = Expr.Meta _ } as t ->
    Util.debug ~section 50 "   > meta";
    if C.mem c t then acc else []
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let l = C.find_top c f in
    Util.debug ~section 50 "   * in %a starting with %a: %a"
      C.debug c Expr.Debug.id f (CCPrint.list Expr.Term.debug) l;
    Util.debug ~section 50 "   * length: %d" (List.length l);
    CCList.flat_map (match_modulo_app acc (ty_pats, pats)) l

let match_modulo = match_modulo_aux [Match.empty]

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

type rule = {
  manual  : bool;
  trigger : Expr.term;
  result  : Expr.formula;
  guard   : Expr.term option;
  formula : Expr.formula;
}

let debug_guard buf = function
  | None -> ()
  | Some e ->
    Printf.bprintf buf "[%a] " Expr.Term.debug e

let debug_rule buf { trigger; result; guard; formula; } =
  Printf.bprintf buf "%a%a --> %a ( %a )"
    debug_guard guard
    Expr.Term.debug trigger
    Expr.Formula.debug result
    Expr.Formula.debug formula

let rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack rules

let rec parse_rule_aux ~manual = function
  (* Equality&Equivalence as rewriting *)
  | ({ Expr.formula = Expr.Equal (a, b) } as f)
  | ({ Expr.formula = Expr.Equiv (
      { Expr.formula = Expr.Pred a },
      { Expr.formula = Expr.Pred b })} as f) ->
    if manual then
      Some { manual; guard = None; trigger = a; result = f; formula = f }
    else begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt ->
        Some { manual; guard = None; trigger = b; result = f; formula = f }
      | Comparison.Gt ->
        Some { manual; guard = None; trigger = a; result = f; formula = f }
    end
  (* Maual rewrite rule for arbitrary formulas *)
  | ({ Expr.formula = Expr.Equiv ({ Expr.formula = Expr.Pred a }, _) } as f) when manual ->
    Some { manual; guard = None; trigger = a; result = f; formula = f }
  (* Polarised rewrite rule as conditional rewrite *)
  | { Expr.formula = Expr.Imply (
      { Expr.formula = Expr.Pred a },
      { Expr.formula = Expr.Pred b })
    } as f ->
    if manual then
      Some { manual; guard = Some a; trigger = a; result = f; formula = f }
    else begin match Lpo.compare a b with
      | Comparison.Gt ->
        Some { manual; guard = Some a; trigger = a; result = f; formula = f }
      | Comparison.Lt | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end
  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred p }, r ) } as f ->
    begin match parse_rule_aux ~manual r with
      | Some ({ guard = None; _ } as rule) ->
        Some { rule with guard = Some p; formula = f }
      | _ -> None
    end
  (* Other formulas are not rewrite rules *)
  | _ -> None

let parse_rule = function
  (* TODO: check that some variabls are actually used in the rule ? *)
  | ({ Expr.formula = Expr.All (_, _, r) } as formula)
  | ({ Expr.formula = Expr.AllTy (_, _, {
         Expr.formula = Expr.All (_, _, r) })} as formula) ->
    let manual = CCOpt.is_some (Expr.Formula.get_tag formula Builtin.Tag.rwrt) in
    begin match parse_rule_aux ~manual r with
      | None ->
        if manual then
          Util.debug ~section 0
            "Following formula couldn't be parsed as a rewrite rule despite tag: %a"
            Expr.Formula.debug r;
        None
      | Some rule ->
        Some { rule with formula }
    end
  | _ -> None

(* Instantiate rewrite rules *)
(* ************************************************************************ *)

let instanciate rule subst =
  let res = Match.formula_apply subst rule.result
  in
  match rule.guard with
  | None ->
    Dispatcher.consequence res [rule.formula]
      (Dispatcher.mk_proof name "rewrite")
  | Some g ->
    let cond = Match.term_apply subst g in
    Dispatcher.watch ~formula:rule.formula name 1 [cond]
      (fun () ->
         let t = Dispatcher.get_assign cond in
         if Expr.Term.equal Builtin.Misc.p_true t then begin
           Dispatcher.consequence res
             [rule.formula; Expr.Formula.pred cond]
             (Dispatcher.mk_proof name "rewrite_cond")
         end
      )

let match_and_instantiate s ({ trigger; _ } as rule) =
  Util.debug ~section 5 "Matches for rule %a" debug_rule rule;
  let seq = T.fold (fun c acc ->
      let repr = C.repr c in
      Util.debug ~section 10 "Trying to match %a with %a"
        Expr.Term.debug trigger C.debug c;
      let s = match_modulo trigger c in
      let s' = List.map (fun x -> repr, x) s in
      List.append s' acc
    ) s [] in
  List.iter (fun (term, subst) ->
      Util.debug ~section 5 "matched '%a' with %a"
        Expr.Debug.term term Match.debug subst;
      instanciate rule subst
    ) seq

(* Rewriter callback *)
(* ************************************************************************ *)

let callback a b t =
  let l = find_all_parents (C.repr t) in
  List.iter (match_and_instantiate l) !rules

(* Rule addition callback *)
(* ************************************************************************ *)

let analyze =
  let rec aux acc = function
    | [] -> acc
    | { manual; _ } :: r ->
      let acc' =
        match acc with
        | None ->
          Some (if manual then `Manual else `Auto)
        | Some `Mixed ->
          Some `Mixed
        | Some `Auto ->
          Some (if manual then `Mixed else `Auto)
        | Some `Manual ->
          Some (if manual then `Manual else `Mixed)
      in
      aux acc' r
  in aux None

(* When adding a new rule, we have to try and instantiate it. *)
let add_rule r =
  let () = rules := r :: !rules in
  (* Check if the set of rules is manual *)
  begin match analyze !rules with
    | None -> assert false (* We just added a rule... *)
    | Some `Manual -> ()
    | Some `Auto -> () (* TODO: complete the rewrite rule system *)
    | Some `Mixed ->
      Util.debug ~section 0
        "Mixed set of rewrite rules detected, removing auto rules";
      rules := List.filter (fun { manual; _ } -> manual) !rules
  end;
  match r.trigger with
  | { Expr.term = Expr.Var _ }
  (** A rewrite rule with a single var as trigger is impossile:
      what term could possibly be smaller than a single variable ? *)
  | { Expr.term = Expr.Meta _ }
    (** A trigger that consist of a single meta does not contain variable,
        thus has no reason to be a rewrite rule... *)
    -> assert false
  | { Expr.term = Expr.App (f, _, _) } ->
    let s = find_indexed f in
    match_and_instantiate s r

(* Plugin *)
(* ************************************************************************ *)

let assume f =
  (* Detect rewrite rules *)
  let () = match parse_rule f with
    | None ->
      Util.debug ~section 50
        "Failed to detect rewrite rule with: %a" Expr.Debug.formula f;
    | Some r ->
      Util.debug ~section 2 "Detected a new rewrite rule: %a" debug_rule r;
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

let register () =
  Ext_eq.register_callback name callback;
  Dispatcher.Plugin.register name
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~peek ~assume ~section ())

