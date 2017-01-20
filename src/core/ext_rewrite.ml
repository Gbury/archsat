
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

let rec match_modulo_app seq (ty_pats, pats) = function
  | { Expr.term = Expr.App (_, ty_args, args) } ->
    let seq' = Sequence.filter_map (match_types ty_pats ty_args) seq in
    let l = List.map Ext_eq.find args in
    List.fold_left2 match_modulo_aux seq' pats l
  | _ -> assert false

and match_modulo_aux seq pat c =
  match pat with
  | { Expr.term = Expr.Var v } ->
    Sequence.filter_map (match_modulo_var v (Ext_eq.repr c)) seq
  | { Expr.term = Expr.Meta _ } as t ->
    if Ext_eq.mem c t then seq else Sequence.empty
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let s = Sequence.of_list (Ext_eq.find_top c f) in
    Sequence.flat_map (match_modulo_app seq (ty_pats, pats)) s

let match_modulo = match_modulo_aux (Sequence.singleton Match.empty)

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

type rule = {
  trigger : Expr.term;
  result  : Expr.term;
  formula : Expr.formula;
  guard   : Expr.formula option;
}

let debug_guard buf = function
  | None -> ()
  | Some e ->
    Printf.bprintf buf "[%a] " Expr.Formula.debug e

let debug_rule buf { trigger; result; guard; formula; } =
  Printf.bprintf buf "%a%a --> %a ( %a )"
    debug_guard guard
    Expr.Term.debug trigger
    Expr.Term.debug result
    Expr.Formula.debug formula

let rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack rules

let rec parse_rule_aux = function
  (* Regular rewrite rule *)
  | ({ Expr.formula = Expr.Equal (a, b) } as f)
  | ({ Expr.formula = Expr.Equiv (
         { Expr.formula = Expr.Pred a },
         { Expr.formula = Expr.Pred b }) } as f) ->
    begin match Lpo.compare a b with
      | Comparison.Incomparable
      | Comparison.Eq -> None
      | Comparison.Lt ->
        Some { guard = None; trigger = b; result = a; formula = f }
      | Comparison.Gt ->
        Some { guard = None; trigger = a; result = b; formula = f }
    end
  (* Polarised rewrite rule *)
  | ({ Expr.formula = Expr.Imply (
         ({ Expr.formula = Expr.Pred a } as g),
         { Expr.formula = Expr.Pred b }) } as f) ->
    begin match Lpo.compare a b with
      | Comparison.Gt ->
        Some { guard = Some g; trigger = a; result = b; formula = f }
      | Comparison.Lt | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end
  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (
      ({ Expr.formula = Expr.Pred p } as g), r ) } as f ->
    begin match parse_rule_aux r with
      | Some ({ guard = None; _ } as rule) ->
        Some { rule with guard = Some g; formula = f }
      | _ -> None
    end
  (* Other formulas are not rewrite rules *)
  | _ -> None

let parse_rule = function
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

(*  *)
(* ************************************************************************ *)

(* Plugin *)
(* ************************************************************************ *)

let name = "rwrt"

let assume f =
  (* Detect rewrite rules *)
  let () = match parse_rule f with
    | None -> ()
    | Some r -> add_rule r
  in
  ()

let register () =
  Dispatcher.Plugin.register name
    ~descr:"Detects rewrite rules and instantiate them (similarly to triggers)"
    (Dispatcher.mk_ext ~section ())

