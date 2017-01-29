
(* Extension name *)
let name = "rwrt"

(* Module initialisation *)
(* ************************************************************************ *)

module S = Set.Make(Expr.Term)
module H = Hashtbl.Make(Expr.Term)

let section = Util.Section.make ~parent:Dispatcher.section "rwrt"

(* Registering parent-child relations between terms *)
(* ************************************************************************ *)

let checked = Tag.create ()
let parents = H.create 42

let find_parents t =
  try H.find parents t
  with Not_found -> S.empty

let add_parent parent child =
  let s = find_parents child in
  H.replace parents child (S.add parent s)

let rec register_parents = function
  (* If the term has already been treated, nothing to do. *)
  | t when Expr.Term.get_tag t checked = Some () -> ()
  (* Else: *)
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (_, _, l) } as t ->
    List.iter (add_parent t) l;
    Expr.Term.tag t checked ();
    List.iter register_parents l

let find_all_parents t =
  let q = Queue.create () in
  let rec aux acc =
    if Queue.is_empty q then acc
    else begin
      let c = Queue.take q in
      let s = Ext_eq.fold (fun s x ->
          let parents = find_parents x in
          S.fold aux_single parents s
        ) acc c in
      aux s
    end
  and aux_single y set =
    let d = Ext_eq.find y in
    let ry = Ext_eq.repr d in
    if S.mem ry set then set
    else begin
      Queue.add d q;
      S.add ry set
    end
  in
  aux (aux_single t S.empty)

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
    let l = List.map Ext_eq.find args in
    List.fold_left2 match_modulo_aux acc' pats l
  | _ -> assert false

and match_modulo_aux acc pat c =
  Util.debug ~section 50 " - matching %a <--> %a"
    Expr.Term.debug pat Ext_eq.debug c;
  match pat with
  | { Expr.term = Expr.Var v } ->
    Util.debug ~section 50 "   > variable";
    CCList.filter_map (match_modulo_var v (Ext_eq.repr c)) acc
  | { Expr.term = Expr.Meta _ } as t ->
    Util.debug ~section 50 "   > meta";
    if Ext_eq.mem c t then acc else []
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let l = Ext_eq.find_top c f in
    Util.debug ~section 50 "   * in %a starting with %a: %a"
      Ext_eq.debug c Expr.Debug.id f (CCPrint.list Expr.Term.debug) l;
    Util.debug ~section 50 "   * length: %d" (List.length l);
    CCList.flat_map (match_modulo_app acc (ty_pats, pats)) l

let match_modulo = match_modulo_aux [Match.empty]

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

type rule = {
  trigger : Expr.term;
  result  : Expr.term;
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
    Expr.Term.debug result
    Expr.Formula.debug formula

let rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack rules

let rec parse_rule_aux = function
  (* Equality as rewriting *)
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt ->
        Some { guard = None; trigger = b; result = a; formula = f }
      | Comparison.Gt ->
        Some { guard = None; trigger = a; result = b; formula = f }
    end
  | { Expr.formula = Expr.Equiv (
      { Expr.formula = Expr.Pred a },
      { Expr.formula = Expr.Pred b })
    } as f ->
    begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt ->
        Some { guard = None; trigger = b; result = a; formula = f }
      | Comparison.Gt ->
        Some { guard = None; trigger = a; result = b; formula = f }
    end
  (* Polarised rewrite rule *)
  | { Expr.formula = Expr.Imply (
      { Expr.formula = Expr.Pred a },
      { Expr.formula = Expr.Pred b })
    } as f ->
    begin match Lpo.compare a b with
      | Comparison.Gt ->
        Some { guard = Some a; trigger = a; result = b; formula = f }
      | Comparison.Lt | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end
  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply ({ Expr.formula = Expr.Pred p }, r ) } as f ->
    begin match parse_rule_aux r with
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
    begin match parse_rule_aux r with
      | None -> None
      | Some rule ->
        Some { rule with formula }
    end
  | _ -> None

let add_rule r =
  Util.debug ~section 2 "Detected a new rewrite rule: %a" debug_rule r;
  rules := r :: !rules

(* Instantiate rewrite rules *)
(* ************************************************************************ *)

let instanciate rule subst =
  let res = Expr.Formula.eq
      (Match.term_apply subst rule.trigger)
      (Match.term_apply subst rule.result)
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

(* Rewriter callback *)
(* ************************************************************************ *)

let callback a b t =
  let l = find_all_parents (Ext_eq.repr t) in
  List.iter (fun ({ trigger; _ } as rule) ->
      Util.debug ~section 5 "Matches for rule %a" debug_rule rule;
      let seq = S.fold (fun repr acc ->
          let c = Ext_eq.find repr in
          Util.debug ~section 10 "Trying to match %a with %a"
            Expr.Term.debug trigger Ext_eq.debug c;
          let s = match_modulo trigger c in
          let s' = List.map (fun x -> repr, x) s in
          List.append s' acc
        ) l [] in
      List.iter (fun (term, subst) ->
          Util.debug ~section 5 "matched '%a' with %a"
            Expr.Debug.term term Match.debug subst;
          instanciate rule subst
        ) seq
    ) !rules

(* Plugin *)
(* ************************************************************************ *)

let assume f =
  (* Detect rewrite rules *)
  let () = match parse_rule f with
    | None -> ()
    | Some r -> add_rule r
  in
  ()

let rec peek = function
  | { Expr.formula = Expr.Pred p } ->
    register_parents p
  | { Expr.formula = Expr.Equal (a, b) } ->
    register_parents a;
    register_parents b
  | { Expr.formula = Expr.Not f } ->
    peek f
  | _ -> ()

let register () =
  Ext_eq.register_callback name callback;
  Dispatcher.Plugin.register name
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~peek ~assume ~section ())

