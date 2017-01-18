
(* Module initialisation *)
(* ************************************************************************ *)

module S = Set.Make(Expr.Term)
module H = Hashtbl.Make(Expr.Term)

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

(* Matching modulo equivalence classes *)
(* ************************************************************************ *)

let match_types pats args subst =
  try Some (List.fold_left2 Unif.Match.ty subst args pats)
  with
  | Unif.Match.Impossible_ty _ -> None
  | Unif.Match.Impossible_term _ -> assert false

let match_modulo_meta m c subst =
  match Unif.get_term_opt subst m with
  | None ->
    Some (Unif.bind_term subst m c)
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
  | { Expr.term = Expr.Var _ } -> assert false
  | { Expr.term = Expr.Meta m } ->
    Sequence.filter_map (match_modulo_meta m (Ext_eq.repr c)) seq
  | { Expr.term = Expr.App (f, ty_pats, pats) } ->
    let s = Sequence.of_list (Ext_eq.find_top c f) in
    Sequence.flat_map (match_modulo_app seq (ty_pats, pats)) s

let match_modulo = match_modulo_aux (Sequence.singleton Unif.empty)

(* Detecting Rewrite rules *)
(* ************************************************************************ *)

let rules = ref []
let () = Backtrack.Stack.attach Dispatcher.stack rules

type rule = {
  trigger : Expr.term;
  formula : Expr.formula;
  guard   : Expr.formula option;
}

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
        Some { guard = None; trigger = b; formula = f }
      | Comparison.Gt ->
        Some { guard = None; trigger = a; formula = f }
    end
  (* Polarised rewrite rule *)
  | ({ Expr.formula = Expr.Imply (
         ({ Expr.formula = Expr.Pred a } as g),
         { Expr.formula = Expr.Pred b }) } as f) ->
    begin match Lpo.compare a b with
      | Comparison.Gt ->
        Some { guard = Some g; trigger = a; formula = f }
      | Comparison.Lt | Comparison.Eq
      | Comparison.Incomparable ->
        None
    end
  (* Conditional rewriting *)
  | { Expr.formula = Expr.Imply (
      ({ Expr.formula = Expr.Pred p } as g), r ) } as f ->
    begin match parse_rule_aux r with
      | Some { guard = None; trigger; _ } ->
        Some { guard = Some g; trigger; formula = f }
      | _ -> None
    end
  (* Other formulas are not rewrite rules *)
  | _ -> None

let parse_rule_term = function
  | { Expr.formula = Expr.All (vars, _, r) } as f ->
    begin match parse_rule_aux r with
      | None -> None
      | Some { guard; trigger; _ } ->
        let metas = List.map Expr.Term.of_meta (Expr.Meta.of_all f) in
        let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty vars metas in
        Some { formula = f;
               trigger = Expr.Term.subst Expr.Subst.empty subst trigger;
               guard = CCOpt.map (Expr.Formula.subst Expr.Subst.empty subst) guard;
             }
    end
  | _ -> None

(* Plugin *)
(* ************************************************************************ *)

let register () =
  ()
