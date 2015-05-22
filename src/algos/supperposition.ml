(*
   This module uses unitary supperposition to
   unify terms modulo equality.
   For a reference, see :
   'E, a brainiac theorem prover' by shulz.
*)

let log_section = Util.Section.make "supp"
let log i fmt = Util.debug ~section:log_section i fmt

(* Clauses *)
(* ************************************************************************ *)

(* Type for unit clauses, i.e clauses with at most one equation *)
type clause = {
  eq : bool; (* is it an equality clause ? *)
  size : int;
  lit : (Expr.Term.t * Expr.Term.t) option;
  acc : Unif.t list;
  parents : clause list;
}

let compare_cl c c' =
  match c.lit, c'.lit with
  | None, Some _ -> -1
  | Some _, None -> 1
  | None, None -> Util.lexicograph Unif.compare c.acc c'.acc
  | Some (a, b), Some (a', b') ->
    match c.eq, c'.eq with
    | true, false -> -1
    | false, true -> 1
    | _ -> begin match Expr.Term.compare a a' with
        | 0 -> begin match Expr.Term.compare b b' with
            | 0 ->  Util.lexicograph Unif.compare c.acc c'.acc
            | x -> x
          end
        | x -> x
      end

let debug_cl buf c =
  match c.lit with
  | None -> Printf.bprintf buf "[]"
  | Some (a, b) -> Printf.bprintf buf "[%a %s %a]"
                     Expr.Debug.term a
                     (if c.eq then "=" else "<>")
                     Expr.Debug.term b

let rec term_size = function
  | { Expr.term = Expr.App (_, _, l) } ->
    1 + List.fold_left (fun acc t -> acc + (term_size t)) 0 l
  | _ -> 1

let tsize a b = term_size a + term_size b

(* TODO: better heuristic for clause selection. *)
let c_leq c c' = c.size <= c'.size

let add_acc x l = CCList.sorted_merge_uniq ~cmp:Unif.compare l [x]
let merge_acc = CCList.sorted_merge_uniq ~cmp:Unif.compare

(* Clauses *)
let mk_cl p lit size acc parents = {
  eq = p;
  lit;
  size;
  acc = List.sort Unif.compare acc;
  parents;
}

let ord a b = if Expr.Term.compare a b <= 0 then a, b else b, a

let mk_eq a b = mk_cl true (Some (ord a b)) (tsize a b)

let mk_neq a b = mk_cl false (Some (ord a b)) (tsize a b)

let mk_none = mk_cl true None 0

(* Indexes *)
(* ************************************************************************ *)

type side = Left | Right

let compare_side a b = match a, b with
  | Left, Left | Right, Right -> 0
  | Left, Right -> -1 | Right, Left -> 1

type pos_cl = {
  pos : Position.Term.t;
  side : side;
  clause : clause;
}

let compare_pos_cl pc pc' =
  match compare_cl pc.clause pc'.clause with
  | 0 -> begin match compare_side pc.side pc'.side with
      | 0 -> Position.Term.compare pc.pos pc'.pos
      | x -> x
    end
  | x -> x


(* Supperposition state *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)
module Q = CCHeap.Make(struct type t = clause let leq = c_leq end)
module S = Set.Make(struct type t = clause let compare = compare_cl end)
module I = Index.Make(struct type t = pos_cl let compare = compare_pos_cl end)

type t = {
  queue : Q.t;
  clauses : S.t;
  root_pos_index : I.t;
  root_neg_index : I.t;
  inactive_index : I.t;
  continuation : Unif.t list -> unit;
}

let empty f = {
  queue = Q.empty;
  clauses = S.empty;
  root_pos_index = I.empty;
  root_neg_index = I.empty;
  inactive_index = I.empty;
  continuation = f;
}

let mem_clause c t = S.mem c t.clauses

let fold_subterms f e side clause i =
  Position.Term.fold (fun i pos t -> match t with
      | { Expr.term = Expr.Meta _ } -> i
      | _ -> f t { pos; side; clause } i) i e

let change_state f_set f_index c t =
  let a, b = match c.lit with
    | Some (a, b) -> a, b
    | None -> assert false
  in
  let l = match Lpo.compare a b with
    | Comparison.Lt -> [b, Right] | Comparison.Gt -> [a, Left]
    | Comparison.Incomparable -> [a, Left; b, Right]
    | Comparison.Eq -> []
  in
  {
    queue = t.queue;
    clauses = f_set c t.clauses;
    root_pos_index =
      if c.eq then
        List.fold_left (fun i (t, side) ->
            f_index t { pos = Position.Term.root; side; clause = c } i)
          t.root_pos_index l
      else
        t.root_pos_index;
    root_neg_index =
      if not c.eq then
        List.fold_left (fun i (t, side) ->
            f_index t { pos = Position.Term.root; side; clause = c } i)
          t.root_neg_index l
      else
        t.root_neg_index;
    inactive_index =
      List.fold_left (fun i (t, side) ->
          fold_subterms f_index t side c i) t.inactive_index l;
    continuation = t.continuation;
  }

let add_clause = change_state S.add I.add
let rm_clause = change_state S.remove I.remove

(* Instanciations constraints *)
(* ************************************************************************ *)

module MS = CCMultiSet.Make(struct
    type t = Expr.Ty.t Expr.Meta.t let compare = Expr.Meta.compare end)

let count c =
  List.fold_left (fun s u ->
      Expr.Subst.fold (fun m t s' ->
          MS.add s' m) u.Unif.t_map s)
    MS.empty c.acc

let check_occ b n m =
  match m.Expr.meta_mult with
  | Expr.Linear -> b && n <= 1
  | Expr.Infinite -> b

let valid_cl c = MS.fold (count c) true check_occ

let push_cl c acc = if valid_cl c then c :: acc else acc

let valid_subst u = (* Check that only meta-var of infinite multiplicity are instantiated *)
  Expr.Subst.for_all (fun m _ -> match m.Expr.meta_mult with
      | Expr.Linear -> false | Expr.Infinite -> true) u.Unif.t_map

(* Help functions *)
(* ************************************************************************ *)

let extract cl =
  match cl.side, cl.clause.lit with
  | Left, Some (a, b) | Right, Some (b, a) -> a, b
  | _, None -> assert false

let do_supp acc sigma active inactive =
  assert (active.clause.eq && active.pos = Position.Term.root);
  let aux = Unif.term_subst sigma in
  let s, t = extract active in
  let u, v = extract inactive in
  let v' = aux v in
  if Lpo.compare (aux t) (aux s) = Comparison.Gt ||
     Lpo.compare v' (aux u) = Comparison.Gt then
    acc
  else
    let u' = aux (Position.Term.substitute inactive.pos t u) in
    let c = mk_cl inactive.clause.eq (Some (ord u' v')) (tsize u' v')
        (add_acc sigma (merge_acc inactive.clause.acc active.clause.acc))
        [active.clause; inactive.clause]
    in
    push_cl c acc

let find_subst_eq index v w =
  List.fold_left (fun acc (_, sigma, l) ->
      if acc = None then
        List.fold_left (fun acc pos_cl ->
            if acc = None && pos_cl.clause.eq then
              let s, t = extract pos_cl in
              try Some (Unif.robinson_term sigma w t)
              with Unif.Not_unifiable_ty _ | Unif.Not_unifiable_term _ -> None
            else acc) acc l
      else acc
    ) None (I.unify v index)

let rec make_eq p_set a b =
  if Expr.Term.equal a b then
    `Equal
  else
    match find_subst_eq p_set.root_pos_index a b with
    | Some u when valid_subst u -> `Unifiable u
    | _ ->
      begin match a, b with
        | { Expr.term = Expr.App (f, _, f_args) }, { Expr.term = Expr.App (g, _, g_args) }
          when Expr.Var.equal f g ->
          make_eq_list p_set f_args g_args
        | _ -> `Impossible
      end

and make_eq_list p_set l l' = match l, l' with
  | [], [] -> `Equal
  | a :: r, b :: r' -> begin match make_eq p_set a b with
      | `Equal -> make_eq_list p_set r r'
      | `Impossible -> `Impossible
      | `Unifiable u ->
        if List.for_all2 Expr.Term.equal r r' then
          `Unifiable u
        else
          `Impossible
    end
  | _ -> invalid_arg "make_eq"

(* Inference rules *)
(* ************************************************************************ *)

(* Equality resolution, alias ER *)
let equality_resolution c =
  if not c.eq then
    match c.lit with
    | Some (a, b) ->
      begin match Unif.find_unifier a b with
        | Some u -> [mk_none (u :: c.acc) [c]]
        | None -> []
      end
    | _ -> []
  else []

(* Supperposition rules, alias SN & SP *)
let add_passive_supp p_set clause side acc pos = function
  | { Expr.term = Expr.Meta _ } -> acc
  | p ->
    let l = I.unify p p_set.root_pos_index in
    let inactive = { clause; side; pos } in
    List.fold_left (fun acc (_, u, l) ->
        List.fold_left (fun acc active ->
            do_supp acc u active inactive
          ) acc l
      ) acc l

let add_active_supp p_set clause side s acc =
  let l = I.unify s p_set.inactive_index in
  let active = { clause; side; pos = Position.Term.root } in
  List.fold_left (fun acc (_, u, l) ->
      List.fold_left (fun acc inactive ->
          do_supp acc u active inactive
        ) acc l
    ) acc l

let supp_lit c p_set acc =
  let a, b = match c.lit with Some(a, b) -> a, b | None -> assert false in
  if c.eq then
    match Lpo.compare a b with
    | Comparison.Gt ->
      add_active_supp p_set c Left a (Position.Term.fold (add_passive_supp p_set c Left) acc a)
    | Comparison.Lt ->
      add_active_supp p_set c Right b (Position.Term.fold (add_passive_supp p_set c Right) acc b)
    | Comparison.Incomparable ->
      add_active_supp p_set c Left a
        (add_active_supp p_set c Right b
           (Position.Term.fold (add_passive_supp p_set c Left)
              (Position.Term.fold (add_passive_supp p_set c Right) acc b) a))
    | Comparison.Eq -> assert false (* trivial cl should have been filtered *)
  else begin
    match Lpo.compare a b with
    | Comparison.Gt -> Position.Term.fold (add_passive_supp p_set c Left) acc a
    | Comparison.Lt -> Position.Term.fold (add_passive_supp p_set c Right) acc b
    | Comparison.Incomparable ->
      Position.Term.fold (add_passive_supp p_set c Left)
        (Position.Term.fold (add_passive_supp p_set c Right) acc b) a
    | Comparison.Eq -> acc (* not much to do... *)
  end

(* rewriting of negative litterals, alis RN *)
let rewrite_neg_lit p_set c =
  if not c.eq then
    match c.lit with
    | None -> None
    | Some (a, b) ->
      Position.Term.fold (fun acc pos p -> acc) None a
  else
    None

(* equality_subsumption, alias ES *)
let equality_subsumption c p_set = (* is there a more generic equality in p_set ? *)
  c.eq && match c.lit with
  | None -> false
  | Some (a, b) -> begin match make_eq p_set a b with
      | `Equal | `Unifiable _ -> true
      | `Impossible -> false
    end

(* positive simplify reflect, alias PS *)
let positive_simplify_reflect p_set c =
  if not c.eq then
    match c.lit with
    | Some (a, b) ->
      begin match make_eq p_set a b with
      | `Equal -> Some (mk_none c.acc c.parents)
      | `Unifiable u -> Some (mk_none (add_acc u c.acc) c.parents)
      | `Impossible -> None
      end
    | None -> None
  else
    None

(* negative simplify reflect, alias NS *)
let negative_simplify_reflect p_set c =
  if c.eq then
    match c.lit with
    | Some (a, b) ->
      begin match find_subst_eq p_set.root_neg_index a b with
        | Some u -> Some (mk_none (add_acc u c.acc) c.parents)
        | None -> None
      end
    | None -> None
  else
    None

(* Main functions *)
(* ************************************************************************ *)

let rec chain l arg =
  match l with
  | [] -> None
  | f :: r -> begin match f arg with
      | Some res -> Some res
      | None -> chain r arg
    end

let fix arg f =
  let rec aux f arg last =
    match f arg with
    | None -> last
    | Some res -> aux f res (Some res)
  in
  aux f arg None

(* Applies: RN, RP, PS (OK), NS (OK) *)
let simplify_clause c p =
  fix c (chain [
      rewrite_neg_lit p;
      positive_simplify_reflect p;
      negative_simplify_reflect p;
    ])

let simplify c p =
  match simplify_clause c p with
  | Some c' -> c'
  | None -> c

(* Applies: RN, RP *)
let cheap_simplify_aux c p =
  fix c (chain [
      rewrite_neg_lit p;
    ])

let cheap_simplify c p =
  match cheap_simplify_aux c p with
  | Some c' -> c'
  | None -> c

(* Applies: ES (OK) *)
let redundant c p = equality_subsumption c p

(* Applies: ER,SP,SN (OK-ALL) *)
let generate c p = supp_lit c p (equality_resolution c)

(* Applies: TD1 (OK) *)
let trivial c p =
  match c.eq, c.lit with
  | true, Some (a, b) when Expr.Term.equal a b -> true
  | _ -> mem_clause c p

let not_is_descendant p c = not (List.memq p c.parents)

(* Main loop *)
(* ************************************************************************ *)

let rec discount_loop p_set =
  match Q.take p_set.queue with
  | None -> p_set
  | Some (u, c) ->
    let c = simplify c p_set in
    if redundant c p_set then begin
      log 20 "Redundant clause : %a" debug_cl c;
      discount_loop { p_set with queue = u }
    end else begin
      log 15 "Adding clause : %a" debug_cl c;
      if c.lit = None then begin
        log 10 "Inst reached, %d clauses in state" (S.cardinal p_set.clauses);
        p_set.continuation c.acc;
        discount_loop { p_set with queue = u }
      end else begin
        let p_set = add_clause c p_set in
        let p_set, t, u = S.fold (fun p (p_set, t, queue) ->
            let p_aux = rm_clause p p_set in
            match simplify_clause p p_aux with
            | None -> (p_set, t, queue)
            | Some p' ->
              (p_aux, S.add p' t, Q.filter (not_is_descendant p) queue)
          ) p_set.clauses (p_set, S.empty, u) in
        let l = generate c p_set in
        let t = List.fold_left (fun s p -> S.add p s) t l in
        let u = S.fold (fun p acc ->
            let p = cheap_simplify p p_set in
            if trivial p p_set then
              acc
            else begin
              log 30 " |- %a" debug_cl p;
              Q.insert p acc
            end
          ) t u in
        discount_loop { p_set with queue = u }
      end
    end

(* Wrappers/Helpers for unification *)
(* ************************************************************************ *)

let add_eq t a b =
  let c = mk_eq a b [] [] in
  if trivial c t then t
  else { t with queue = Q.insert c t.queue }

let add_neq t a b = { t with queue = Q.insert (mk_neq a b [] []) t.queue }

let solve t = discount_loop t

