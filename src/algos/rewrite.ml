(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make "rewrite"

(* Rewrite rules guards *)
(* ************************************************************************ *)

module Guard = struct

  type t =
    | Pred_true of Expr.term
    | Pred_false of Expr.term
    | Eq of Expr.term * Expr.term
    | Neq of Expr.term * Expr.term

  let print ?(term=Expr.Print.term) fmt = function
    | Pred_true p ->
      Format.fprintf fmt "%a" term p
    | Pred_false p ->
      Format.fprintf fmt "~ %a" term p
    | Eq (a, b) ->
      Format.fprintf fmt "%a=%a" term a term b
    | Neq (a, b) ->
      Format.fprintf fmt "%a!=%a" term a term b

  let map f = function
    | Pred_true p -> Pred_true (f p)
    | Pred_false p -> Pred_false (f p)
    | Eq (a, b) -> Eq (f a, f b)
    | Neq (a, b) -> Neq (f a, f b)

  let to_list = function
    | Pred_true p -> [p]
    | Pred_false p -> [p]
    | Eq (a, b) -> [a; b]
    | Neq (a, b) -> [a; b]

  let check = function
    | Pred_true p -> Expr.Term.equal p Builtin.Misc.p_true
    | Pred_false p -> Expr.Term.equal p Builtin.Misc.p_false
    | Eq (a, b) -> Expr.Term.equal a b
    | Neq (a, b) -> not @@ Expr.Term.equal a b

  let fv = function
    | Pred_true p | Pred_false p ->
      Expr.Term.fv p
    | Eq (a, b) | Neq (a, b) ->
      Expr.Id.merge_fv (Expr.Term.fv a) (Expr.Term.fv b)

  let fv_list =
    let rec aux acc = function
      | [] -> acc
      | g :: r -> aux (Expr.Id.merge_fv acc (fv g)) r
    in
    aux ([], [])

end

(* Rewrite rules definition *)
(* ************************************************************************ *)

module Rule = struct

  type 'a witness =
    | Term : Expr.term witness
    | Formula : Expr.formula witness

  type 'a rewrite = {
    trigger : 'a;
    result : 'a;
  }

  type contents = C : 'a witness * 'a rewrite -> contents

  type t = {
    id       : int;
    manual   : bool;
    formula  : Expr.formula;
    guards   : Guard.t list;
    contents : contents;
  }

  (* Std functions *)
  let hash r = r.id
  let compare r r' = compare r.id r'.id
  let equal r r' = compare r r' = 0

  (* Printing functions *)
  let rec print_guards ?term fmt = function
    | [] -> ()
    | g :: r ->
      Format.fprintf fmt "@[<hov>[%a]@,%a@]"
        (Guard.print ?term) g (print_guards ?term) r

  let print_id fmt r =
    Format.fprintf fmt "%s%d" (if r.manual then "~" else "#") r.id

  let print_rewrite pp fmt {trigger; result} =
    Format.fprintf fmt "{@[<hv>%a@ ↦ %a@]}" pp trigger pp result

  let print_contents
      ?(term=Expr.Print.term)
      ?(formula=Expr.Print.formula)  fmt = function
    | C (Term, rewrite) -> print_rewrite term fmt rewrite
    | C (Formula, rewrite) -> print_rewrite formula fmt rewrite

  let print
      ?(term=Expr.Print.term)
      ?(formula=Expr.Print.formula)
      fmt ({ guards; formula = f; contents; _ } as rule) =
    Format.fprintf fmt "@[<hv 2>%a@ %a@ %a@ (%a)@]"
      print_id rule
      (print_guards ~term) guards
      (print_contents ~term ~formula) contents
      formula f

  let error_fv s r (l, l') =
    if l = [] && l' = [] then () else
      Util.error ~section
        "@[<hv>Created rewrite rule with unbound variables in %s:@ @[<hov>%a@ %a@]@ in@ %a@]"
        s
        CCFormat.(list ~sep:(return "@ ") Expr.Id.print) l
        CCFormat.(list ~sep:(return "@ ") Expr.Id.print) l'
        (print ~term:Expr.Term.print ~formula:Expr.Formula.print) r

  (* convenience function *)
  let fv_of_witness
    : type a. a witness -> (a -> Expr.Id.Ttype.t list * Expr.Id.Ty.t list)
    = function
    | Term -> Expr.Term.fv
    | Formula -> Expr.Formula.fv

  (* Rule creation *)
  let _nb_rules = ref 0
  let mk_aux witness ?(guards=[]) manual trigger result =
    let () = incr _nb_rules in
    let fv = fv_of_witness witness in
    let r = {
      id = !_nb_rules; manual; guards;
      formula = Expr.Formula.f_true;
      contents = C (witness, {trigger; result; });
    } in
    let v_g = Guard.fv_list guards in
    let v_t = fv trigger in
    let v_r = fv result in
    error_fv "conditions" r (Expr.Id.remove_fv v_g v_t);
    error_fv "result" r (Expr.Id.remove_fv v_r v_t);
    r

  let mk_term = mk_aux Term
  let mk_formula = mk_aux Formula

  (* Some queries/manipulation of rules *)
  let is_manual { manual; } = manual

  let add_guards guards rule =
    let r = { rule with guards = guards @ rule.guards } in
    let v_t =
      match rule.contents with
      | C (Term, { trigger; _}) -> Expr.Term.fv trigger
      | C (Formula, { trigger; _}) -> Expr.Formula.fv trigger
    in
    let v_g = Guard.fv_list guards in
    error_fv "conditions" r (Expr.Id.remove_fv v_g v_t);
    r

  let set_formula formula rule =
    { rule with formula }

end

(* Rule substitution *)
(* ************************************************************************ *)

module Subst = struct

  type t = {
    rule : Rule.t;
    inst : Mapping.t;
    pos  : Position.t;
  }

  let mk rule inst pos = { rule; inst; pos; }

  let print fmt { rule; inst; pos; } =
    Format.fprintf fmt "@[<hv>%a@ %a@ @@%a@]"
      (Rule.print ~term:Expr.Term.print ~formula:Expr.Formula.print) rule
      Mapping.print inst Position.print pos

  let map_rewrite f { Rule.trigger; result; } =
    { Rule.trigger = f trigger; result = f result; }

  let rule { rule; _} = rule
  let inst { inst; _ } = inst

  let formula s = (rule s).Rule.formula

  let info { rule; inst; _ } =
    match rule.Rule.contents with
    | Rule.C (Rule.Term, r) ->
      Rule.C (Rule.Term, map_rewrite (Mapping.apply_term inst) r)
    | Rule.C (Rule.Formula, r) ->
      Rule.C (Rule.Formula, map_rewrite (Mapping.apply_formula inst) r)

end

(* Normalization by rules (no matching modulo eq) *)
(* ************************************************************************ *)


module Normalize = struct

  let match_term_head t rules =
    let aux t rule =
      if rule.Rule.guards = [] then
        match rule.Rule.contents with
        (* SKip formula rewrite rules *)
        | Rule.C (Rule.Formula, _) -> None
        (** Match&instanciate on terms *)
        | Rule.C (Rule.Term, { Rule.trigger = pat; result = res; }) ->
          begin match Match.term Mapping.empty pat t with
            | m ->
              Some (rule, m, Mapping.apply_term ~fix:false m res)
            | exception Match.Impossible_ty _ -> None
            | exception Match.Impossible_term _ -> None
          end
      else begin
        Util.warn  "conditional rewrite rule";
        None
      end
    in
    CCList.find_map (aux t) rules

  let find_term_match rules t =
    let aux pos t' =
      let aux (rule, m, res) = (rule, m, res, pos) in
      CCOpt.map aux (match_term_head t' rules)
    in
    Position.Term.find_map aux t

  let rec normalize_term rules acc t =
    match find_term_match rules t with
    | None -> t, List.rev acc
    | Some (rule, m, res, pos) ->
      begin match Position.Term.substitute pos ~by:res t with
        | None -> assert false
        | Some res ->
          let subst = Subst.mk rule m pos in
          normalize_term rules (subst :: acc) res
      end

  let match_atomic f rules =
    let aux f rule =
      if rule.Rule.guards = [] then
        match rule.Rule.contents with
        (* Skip formula rewrite rules *)
        | Rule.C (Rule.Term, _) -> None
        (** Match&instanciate on terms *)
        | Rule.C (Rule.Formula, { Rule.trigger = pat; result = res; }) ->
          begin match Match.atomic Mapping.empty pat f with
            | m ->
              Some (Subst.mk rule m Position.root,
                    Mapping.apply_formula ~fix:false m res)
            | exception Match.Impossible_ty _ -> None
            | exception Match.Impossible_term _ -> None
            | exception Match.Impossible_atomic _ -> None
          end
      else begin
        Util.warn  "conditional rewrite rule";
        None
      end
    in
    CCList.find_map (aux f) rules

  let rec normalize_atomic rules acc f =
    match match_atomic f rules with
    | Some (s, res) ->
      normalize_atomic rules (s :: acc) res
    | None ->
      begin match f with
        | { Expr.formula = Expr.Not p } ->
          let p', acc = normalize_atomic rules acc p in
          if p == p' then f, List.rev acc
          else normalize_atomic rules acc (Expr.Formula.neg p')
        | { Expr.formula = Expr.Pred t } ->
          let t', acc = normalize_term rules acc t in
          if t == t' then f, List.rev acc
          else normalize_atomic rules acc (Expr.Formula.pred t')
        | { Expr.formula = Expr.Equal (a, b) } ->
          let a', acc = normalize_term rules acc a in
          let b', acc = normalize_term rules acc b in
          if a == a' && b == b' then f, List.rev acc
          else normalize_atomic rules acc (Expr.Formula.eq a' b')
        | _ -> f, List.rev acc
      end

end

(* Narrowing by rules (no matching modulo eq) *)
(* ************************************************************************ *)


module Narrow = struct

  let _true _ _ = true
  let _false _ _ = false
  let _nope  _ _ = assert false

  let new_tyvar, new_var =
    let r = ref 0 in
    (fun _ -> incr r; Expr.Id.ttype (Format.asprintf "r_%d" !r)),
    (fun ty -> incr r; Expr.Id.ty (Format.asprintf "r_%d" !r) ty)

  let find (type a) (e: a)
      (witness: a Rule.witness)
      (rewrite: a Rule.rewrite) =
    let unify : a -> a -> Mapping.t list =
      match witness with
      | Rule.Term -> (fun t t' -> [Unif.Robinson.term Mapping.empty t t'])
      | Rule.Formula -> Unif.Robinson.atomic Mapping.empty
    in
    match unify rewrite.Rule.trigger e with
    | [] -> assert false
    | exception Unif.Robinson.Impossible_ty _ -> []
    | exception Unif.Robinson.Impossible_term _ -> []
    | exception Unif.Robinson.Impossible_atomic _ -> []
    | l ->
      Util.debug ~section "@[<hv 2>Found unifiers:@ %a"
        CCFormat.(list ~sep:(return "@ ") Mapping.print) l;
      (* Compute the free_variables of the trigger *)
      let fv_ty, fv_t =
        match witness, rewrite with
        | Rule.Term, { Rule.trigger } -> Expr.Term.fv trigger
        | Rule.Formula, { Rule.trigger } -> Expr.Formula.fv trigger
      in
      (* Strip away pure rule instanciations. *)
      let l' = List.filter (fun m ->
          let _, (fm_ty, fm_t) = Mapping.domain m in
          let res = not (fm_ty = [] && fm_t = []) in
          if not res then Util.debug ~section "filtering out %a" Mapping.print m;
          res
        ) l in
      (** Replace variables (all of which should come from the rewrite rule),
          by fresh one to avoid strange capture things. Additionally, each
          narrowing instance should use distinct fresh variables. *)
      let freshen subst =
        (* check that every remaining free var in the subst comes from the trigger*)
        assert (
          let ((ty_var, t_var), _) = Mapping.codomain subst in
          List.for_all (fun v -> List.exists (Expr.Id.equal v) fv_t) t_var &&
          List.for_all (fun v -> List.exists (Expr.Id.equal v) fv_ty) ty_var
        );
        (* create some fresh variables for the free vars in the trigger *)
        let m = List.fold_left (fun acc v ->
            Mapping.Var.bind_term acc v (Expr.Term.of_id (new_var (
                Mapping.apply_ty acc v.Expr.id_type)))
          ) (List.fold_left (fun acc v ->
            if Mapping.Var.mem_ty subst v
            then Mapping.Var.bind_ty acc v (Mapping.Var.get_ty subst v)
            else Mapping.Var.bind_ty acc v (Expr.Ty.of_id (new_tyvar v))
          ) Mapping.empty fv_ty) fv_t in
        Util.debug ~section "@[<hv 2>freshening:@ %a@ with %a@]"
          Mapping.print subst Mapping.print m;
        (* replace old vars by the new variables in the bound terms. No need
           to bind the new vars since only the metas should be substituted. *)
        Mapping.filter subst
          ~ty_var:_true ~term_var:_true
          ~ty_meta:_false ~term_meta:_false
          ~formula_var:_nope ~formula_meta:_nope,
        Mapping.fixpoint @@
        Mapping.apply m @@
        Mapping.filter subst
          ~ty_var:_false ~term_var:_false
          ~ty_meta:_true ~term_meta:_true
          ~formula_var:_nope ~formula_meta:_nope
      in
      List.map freshen l'

  let term_aux t rule =
    match rule.Rule.contents with
    | Rule.C (Rule.Formula, _) -> []
    | Rule.C (Rule.Term, rewrite) ->
      Util.debug ~section "@[<hv 2>Narrowing@ %a@ with %a@]"
       (Rule.print_rewrite Expr.Term.print) rewrite Expr.Term.print t;
      let l = find t Rule.Term (rewrite: Expr.term Rule.rewrite) in
      List.map (fun (m, m') -> rule, m, m') l

  let formula_aux f rule =
    match rule.Rule.contents with
    | Rule.C (Rule.Term, _) -> []
    | Rule.C (Rule.Formula, rewrite) ->
      Util.debug ~section "@[<hv 2>Narrowing@ %a@ with %a@]"
       (Rule.print_rewrite Expr.Formula.print) rewrite Expr.Formula.print f;
      let l = find f Rule.Formula (rewrite: Expr.formula Rule.rewrite) in
      List.map (fun (m, m') -> rule, m, m') l

  let term t rules =
    CCList.flat_map (term_aux t) rules

  let formula f rules =
    CCList.flat_map (formula_aux f) rules

end
