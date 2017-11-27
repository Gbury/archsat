
(* Rewrite rules guards *)
(* ************************************************************************ *)

module Guard = struct

  type t =
    | Pred_true of Expr.term
    | Pred_false of Expr.term
    | Eq of Expr.term * Expr.term

  let print ?(term=Expr.Print.term) fmt = function
    | Pred_true p ->
      Format.fprintf fmt "%a" term p
    | Pred_false p ->
      Format.fprintf fmt "~ %a" term p
    | Eq (a, b) ->
      Format.fprintf fmt "%a=%a" term a term b

  let map f = function
    | Pred_true p -> Pred_true (f p)
    | Pred_false p -> Pred_false (f p)
    | Eq (a, b) -> Eq (f a, f b)

  let to_list = function
    | Pred_true p -> [p]
    | Pred_false p -> [p]
    | Eq (a, b) -> [a; b]

  let check = function
    | Pred_true p -> Expr.Term.equal p Builtin.Misc.p_true
    | Pred_false p -> Expr.Term.equal p Builtin.Misc.p_false
    | Eq (a, b) -> Expr.Term.equal a b

end

(* Rewrite rules triggers *)
(* ************************************************************************ *)

module Trigger = struct

  type t =
    | Single of Expr.term
    | Equal of Expr.term * Expr.term

  let print ?(term=Expr.Print.term) fmt = function
    | Single x -> term fmt x
    | Equal (x, y) -> Format.fprintf fmt "%a ==@ %a" term x term y

end

(* Rewrite rules definition *)
(* ************************************************************************ *)

module Rule = struct

  type result =
    | Term of Expr.term
    | Formula of Expr.formula

  type t = {
    id       : int;
    manual   : bool;
    trigger  : Trigger.t;
    result   : result;
    guards   : Guard.t list;
    formula  : Expr.formula;
  }

  (* Std functions *)
  let hash r = r.id
  let compare r r' = compare r.id r'.id
  let equal r r' = compare r r' = 0

  (* Rule creation *)
  let _nb_rules = ref 0
  let mk ?(guards=[]) manual trigger result =
    let () = incr _nb_rules in
    { id = !_nb_rules; manual; trigger; result; guards; formula = Expr.Formula.f_true; }

  (* Some queries/manipulation of rules *)
  let is_manual { manual; } = manual

  let add_guards guards rule =
    { rule with guards = guards @ rule.guards }

  let set_formula formula rule =
    { rule with formula }

  (* Printing functions *)
  let rec print_guards ?term fmt = function
    | [] -> ()
    | g :: r ->
      Format.fprintf fmt "@[<hov>[%a]@,%a@]"
        (Guard.print ?term) g (print_guards ?term) r

  let print_id fmt r =
    Format.fprintf fmt "%s%d" (if r.manual then "~" else "#") r.id

  let print_result
      ?(term=Expr.Print.term)
      ?(formula=Expr.Print.formula)
      fmt = function
    | Term t -> term fmt t
    | Formula f -> formula fmt f

  let print
      ?(term=Expr.Print.term)
      ?(formula=Expr.Print.formula)
      fmt ({ trigger; result; guards; formula = f; _ } as rule) =
    Format.fprintf fmt "@[<hv 2>%a@ @[<hov 2>%a@ %a@]@ ->%a@ (%a)@]"
      print_id rule
      (print_guards ~term) guards
      (Trigger.print ~term) trigger
      (print_result ~term ~formula) result
      formula f

end

(* Normalization by rules (no matching modulo eq) *)
(* ************************************************************************ *)


module Normalize = struct

  type finder =
    Rule.t list -> Expr.term ->
    (Rule.t * Expr.term * Position.t) option

  let rec match_head_aux t rule =
    match rule with
    (* Skip conditional rules, as they are quite complex to hande correctly. *)
    | _ when rule.Rule.guards <> [] ->
      Util.warn  "conditional rewrite rule";
      None
    (** Skip rules matching an equality, because we don't really want
        to substitute equalities, rather we'd want to use trigger-style
        rewriting. *)
    | { Rule.trigger = Trigger.Equal _ ; _ } -> None
    (** Skip formula result rewrite rules *)
    | { Rule.result = Rule.Formula _ ; _ } -> None
    (** Finally, the 'usual' case *)
    | { Rule.trigger = Trigger.Single pat ;
        Rule.result = Rule.Term res; _ } ->
      begin match Match.term Mapping.empty pat t with
        | m ->
          Some (rule, Mapping.apply_term ~fix:false m res)
        | exception Match.Impossible_ty _ -> None
        | exception Match.Impossible_term _ -> None
      end

  let match_head t rules =
    CCList.find_map (match_head_aux t) rules

  let match_any_aux rules = fun pos t' ->
    CCOpt.map (fun (rule, res) -> (rule, res, pos)) (match_head t' rules)

  let top_down rules t =
    Position.Term.find_map (match_any_aux rules) t

  let rec normalize_aux ~find rules acc t =
    match find rules t with
    | None -> List.rev acc, t
    | Some (rule, res, pos) ->
      begin match Position.Term.substitute pos ~by:res t with
        | None -> assert false
        | Some res -> normalize_aux ~find rules (rule :: acc) res
      end

  let normalize ~find rules t = normalize_aux ~find rules [] t

end
