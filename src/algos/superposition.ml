(*
   This module uses unitary supperposition to
   unify terms modulo equality.
   For a reference, see :
   'E, a brainiac theorem prover' by shulz.
*)

(* Types *)
(* ************************************************************************ *)

type side = Left | Right

type lit =
  | Empty
  | Eq of Expr.term * Expr.term
  | Neq of Expr.term * Expr.term

(* Type of reasons for clauses. *)
type reason =
  | Hyp
  | ER of clause
  | SN of pointer * pointer
  | SP of pointer * pointer
  | RN of pointer * pointer
  | RP of pointer * pointer

(* Type for unit clauses, i.e clauses with at most one equation *)
and clause = {
  id : int;                 (* Unique id (for printing and tracking through logs) *)
  lit : lit;                (* Contents of the clause *)
  map : Unif.t;             (* Current mapping for meta-variables *)
  reason : reason;          (* Reason of the clause *)
  weight : int;             (* weight of the clause (clauses with lesser
                               weight are selected first) *)
}

and pointer = {
  clause : clause;
  side : side;
  path : Position.t;
}

(* Substitutions *)
(* ************************************************************************ *)

(* Make substs more easily comparable, i.e.
   idempotent and with predictable ordering of meta to meta bindings *)
let fix s =
  let acc =
    Expr.Subst.fold (fun m ty acc ->
        match Unif.type_subst s ty with
        | { Expr.ty = Expr.TyMeta m' } ->
          let meta, meta' =
            if Expr.Meta.compare m m' < 0 then m, m' else m', m
          in
          Unif.bind_ty acc meta (Expr.Ty.of_meta meta')
        | t -> Unif.bind_ty acc m t
      ) s.Unif.ty_map Unif.empty
  in
  Expr.Subst.fold (fun m term acc ->
      match Unif.term_subst s term with
      | { Expr.term = Expr.Meta m' } ->
        let meta, meta' =
          if Expr.Meta.compare m m' < 0 then m, m' else m', m
        in
        Unif.bind_term acc meta (Expr.Term.of_meta meta')
      | t -> Unif.bind_term acc m t
    ) s.Unif.t_map acc

(* Ordering on substitutions *)
let subst_forall s p_ty p_term =
  Expr.Subst.fold (fun ty_meta ty acc -> acc && p_ty ty_meta ty) s.Unif.ty_map
    (Expr.Subst.fold (fun meta term acc -> acc && p_term meta term) s.Unif.t_map true)

let (<<) s t =
  subst_forall s
    (fun ty_meta ty -> Expr.Ty.equal
        (Unif.type_subst t ty) (Unif.type_subst t (Expr.Ty.of_meta ty_meta)))
    (fun meta term -> Expr.Term.equal
        (Unif.term_subst t term) (Unif.term_subst t (Expr.Term.of_meta meta)))

(* Clauses *)
(* ************************************************************************ *)

(* Misc functions on clauses *)
let is_eq c =
  match c.lit with
  | Eq _ -> true
  | Neq _ | Empty -> false

(* Comparison of clauses *)
let _discr = function
  | Empty -> 0
  | Eq _ -> 1
  | Neq _ -> 2

let compare c c' =
  match c.lit, c'.lit with
  | Empty, Empty ->
    Unif.compare c.map c'.map
  | Eq (a, b), Eq (a', b')
  | Neq (a, b), Neq (a', b') ->
    begin match Expr.Term.compare a a' with
      | 0 -> begin match Expr.Term.compare b b' with
          | 0 ->  Unif.compare c.map c'.map
          | x -> x
        end
      | x -> x
    end
  | x, y -> Pervasives.compare (_discr x) (_discr y)

(* Printing of clauses *)
let pp_id fmt c = Format.fprintf fmt "C%d" c.id

let pp_reason fmt c =
  match c.reason with
  | Hyp -> Format.fprintf fmt "hyp"
  | ER d -> Format.fprintf fmt "ER(%a)" pp_id d
  | SN (d, e) -> Format.fprintf fmt "SN(%a;%a)" pp_id d.clause pp_id e.clause
  | SP (d, e) -> Format.fprintf fmt "SP(%a;%a)" pp_id d.clause pp_id e.clause
  | RN (d, e) -> Format.fprintf fmt "RN(%a;%a)" pp_id d.clause pp_id e.clause
  | RP (d, e) -> Format.fprintf fmt "RP(%a;%a)" pp_id d.clause pp_id e.clause

let pp_lit fmt c =
  match c.lit with
  | Empty -> Format.fprintf fmt "∅"
  | Eq (a, b) -> Format.fprintf fmt "@[%a@ =@ %a@]" Expr.Print.term a Expr.Print.term b
  | Neq (a, b) -> Format.fprintf fmt "@[%a@ ≠@ %a@]" Expr.Print.term a Expr.Print.term b

let pp_map fmt c = Unif.print fmt c.map

let pp fmt (c:clause) =
  Format.fprintf fmt "@[<hov 2>%a@,[%a]@,[%a]@,[%a]@]"
    pp_id c pp_reason c pp_lit c pp_map c

(* Heuristics for clauses. Currently uses the size of terms.
   TODO: better heuristic for clause selection. *)
let rec term_size = function
  | { Expr.term = Expr.App (_, _, l) } ->
    1 + List.fold_left (fun acc t -> acc + (term_size t)) 0 l
  | _ -> 1

let compute_weight = function
  | Empty -> 0
  | Eq (a, b) | Neq (a, b) ->
    term_size a + term_size b

let cmp_weight c c' = c.weight <= c'.weight

(* Clauses *)
let mk_cl =
  let i = ref 0 in
  (fun lit subst reason ->
     incr i;
     let weight = compute_weight lit in
     let map = fix subst in
     { id = !i; lit; map; reason; weight; }
  )

let ord a b = if Expr.Term.compare a b <= 0 then a, b else b, a

let mk_empty map clause =
  mk_cl Empty map (ER clause)

let mk_eq a b map reason =
  let c, d = ord a b in
  mk_cl (Eq (c, d)) map reason

let mk_neq a b map reason =
  let c, d = ord a b in
  mk_cl (Neq (c, d)) map reason

(* Clause pointers *)
(* ************************************************************************ *)

let compare_side a b = match a, b with
  | Left, Left | Right, Right -> 0
  | Left, Right -> -1 | Right, Left -> 1


let compare_pointer pc pc' =
  match compare pc.clause pc'.clause with
  | 0 -> begin match compare_side pc.side pc'.side with
      | 0 -> Position.compare pc.path pc'.path
      | x -> x
    end
  | x -> x

(* Supperposition state *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)
module Q = CCHeap.Make(struct type t = clause let leq = cmp_weight end)
module S = Set.Make(struct type t = clause let compare = compare end)
module I = Index.Make(struct type t = pointer let compare = compare_pointer end)

type rules = {
  er : bool;
  sn : bool;
  sp : bool;
  es : bool;
  rp : bool;
  rn : bool;
}

type t = {
  queue : Q.t;
  clauses : S.t;
  generated : S.t;
  rules : rules;
  root_pos_index : I.t;
  root_neg_index : I.t;
  inactive_index : I.t;
  section : Section.t;
  callback : (Unif.t -> unit);
}

let all_rules = {
  er = true;
  sn = true;
  sp = true;
  es = true;
  rp = true;
  rn = true;
}

let empty ?(rules=all_rules) section callback = {
  queue = Q.empty;
  clauses = S.empty;
  generated = S.empty;
  section; callback; rules;
  root_pos_index = I.empty (Section.make ~parent:section "pos_index");
  root_neg_index = I.empty (Section.make ~parent:section "neg_index");
  inactive_index = I.empty (Section.make ~parent:section "all_index");
}

let fold_subterms f e side clause i =
  Position.Term.fold (fun i path t -> f t { path; side; clause } i) i e

let change_state f_set f_index c t =
  let eq, a, b = match c.lit with
    | Eq (a, b) -> true, a, b
    | Neq (a, b) -> false, a, b
    | Empty -> assert false
  in
  let l = match Lpo.compare a b with
    | Comparison.Lt -> [b, Right] | Comparison.Gt -> [a, Left]
    | Comparison.Incomparable -> [a, Left; b, Right]
    | Comparison.Eq -> []
  in
  { t with
    clauses = f_set c t.clauses;
    root_pos_index =
      if eq then
        List.fold_left (fun i (t, side) ->
            f_index t { path = Position.root; side; clause = c } i)
          t.root_pos_index l
      else
        t.root_pos_index;
    root_neg_index =
      if not eq then
        List.fold_left (fun i (t, side) ->
            f_index t { path = Position.root; side; clause = c } i)
          t.root_neg_index l
      else
        t.root_neg_index;
    inactive_index =
      List.fold_left (fun i (t, side) ->
          fold_subterms f_index t side c i) t.inactive_index l;
  }

let add_clause = change_state S.add I.add
let rm_clause = change_state S.remove I.remove

(* Help functions *)
(* ************************************************************************ *)

let extract pos =
  match pos.side, pos.clause.lit with
  | Left, (Eq (a, b) | Neq (a, b))
  | Right, (Eq (b, a) | Neq (b, a)) -> a, b
  | _, Empty -> assert false

(* Perform an equality resolution, i.e rule ER *)
let do_resolution ~section acc clause =
  match clause.lit with
  | Eq _ | Empty -> acc
  | Neq (s, t) ->
    let sigma = clause.map in
    begin match Unif.Robinson.term sigma s t with
      | sigma' -> mk_empty sigma' clause :: acc
      | exception Unif.Robinson.Impossible_ty _ ->
        Util.debug ~section "Couldn't unify:@ %a =@ %a@;%a"
          Expr.Term.print s Expr.Term.print t Unif.print sigma;
        acc
      | exception Unif.Robinson.Impossible_term _ ->
        Util.debug ~section "Couldn't unify:@ %a =@ %a@;%a"
          Expr.Term.print s Expr.Term.print t Unif.print sigma;
        acc
    end

(* Perform a superposition, i.e either rule SN or SP
   [active] is (the position of) the equality used to perform the substitution,
   [inactive] is (the position of) the clause the substitution is being performed on
   [mgu] is the subtitution that unifies [active] and [inactive]
   TODO: check the LPO constraints iff it really need to be checked
         i.e. only when the ordering failed on the non-instanciated clause
*)
let do_supp acc mgu active inactive =
  assert (is_eq active.clause);
  assert (Position.equal active.path Position.root);
  let p = inactive.path in
  let s, t = extract active in
  let u, v = extract inactive in
  let sigma = active.clause.map in
  let sigma' = inactive.clause.map in
  (* Merge the substitutions. *)
  match CCOpt.(Unif.merge sigma sigma' >>= Unif.merge mgu) with
  | None -> acc
  | Some sigma'' ->
    let apply = Unif.term_subst sigma'' in
    let v' = apply v in
    let u_res, u_p_opt = Position.Term.apply p u in
    (* Chekc that mgu effectively unifies u_p and s *)
    assert (match u_p_opt with
        | None -> false
        | Some u_p ->
          Expr.Term.equal (Unif.term_subst mgu s) (Unif.term_subst mgu u_p));
    (* Check the guards of the rule *)
    if Lpo.compare (apply t) (apply s) = Comparison.Gt ||
       Lpo.compare v' (apply u) = Comparison.Gt ||
       fst (Position.Term.apply p u) = Position.Var then
      acc
    else begin
      (* Apply substitution *)
      match Position.Term.substitute inactive.path ~by:t u with
      | Some tmp ->
        let u' = apply tmp in
        let f = if is_eq inactive.clause then mk_eq else mk_neq in
        let reason =
          if is_eq inactive.clause then
            SP(active, inactive)
          else
            SN(active, inactive)
        in
        let c = f u' v' sigma'' reason in
        c :: acc
      | None ->
        (* This should not happen *)
        assert false
    end

(* Perform a rewrite, i.e. either rule RN or RP
   [active] is the equality used for the rewrite
   [inactive] is the clause being worked on
   [rho] is the substitution that matches [active] and [inactive]
*)
let do_rewrite active inactive =
  (* currently the substitution must be the identity *)
  assert (is_eq active.clause);
  assert (active.path = Position.root);
  let sigma = inactive.clause.map in
  let s, t = extract active in
  let u, v = extract inactive in
  let guard =
    active.clause.map << sigma &&
    Lpo.compare s t = Comparison.Gt &&
    (if is_eq inactive.clause then (
        not (Lpo.compare u v = Comparison.Gt) ||
        not (Position.equal inactive.path Position.root)
      ) else true)
  in
  if not guard then None
  else begin
    match Position.Term.substitute inactive.path ~by:t u with
    | Some u' ->
      let f = if is_eq inactive.clause then mk_eq else mk_neq in
      let reason =
        if is_eq inactive.clause
        then RP(active, inactive)
        else RN(active, inactive)
      in
      Some (f u' v sigma reason)
    | None ->
      (* shouldn't really happen *)
      assert false
  end

(* This functions tries to find an equality [v = w] in the index,
   used particualrly for computing the ES rule. *)
let find_eq index v w =
  CCList.flat_map (fun (_, l) ->
      CCList.flat_map (fun pos ->
          let s, t = extract pos in
          (* should be enforced by the index. *)
          assert (Expr.Term.equal v s);
          if Expr.Term.equal t w then [pos] else []
        ) l) (I.find_equal v index)

(* This function tries and find if there is an equality in p_set, such
   that [a] and [b] are suceptible to be an equality simplified by the ES rule.
   Additionally, for the ES rule, we need to keep track of the position at which
   the subtitution takes place. That is the role of the [curr] argument.
   Returns the list of all potential clauses that could be used to make
   [a] and [b] equal.
*)
let rec make_eq_aux p_set curr a b =
  if Expr.Term.equal a b then `Equal
  else
    match find_eq p_set.root_pos_index a b with
    | [] ->
      begin match a, b with
        | { Expr.term = Expr.App (f, _, f_args) },
          { Expr.term = Expr.App (g, _, g_args) } when Expr.Id.equal f g ->
          make_eq_list p_set curr 0 f_args g_args
        | _ -> `Impossible
      end
    | l -> `Substitutable (curr, l)

and make_eq_list p_set curr idx l l' =
  match l, l' with
  | [], [] -> `Equal
  | a :: r, b :: r' ->
    begin match make_eq_aux p_set (Position.arg idx curr) a b with
      | `Equal -> make_eq_list p_set curr (idx + 1) r r'
      | `Impossible -> `Impossible
      | `Substitutable (path, u) as res ->
        if List.for_all2 Expr.Term.equal r r' then res else `Impossible
    end
  | _ ->
    (* Since we only give arguments list of equal functions, the two lists
       should always have the same length. *)
    assert false

let make_eq p_set a b =
  make_eq_aux p_set Position.root a b

(* Inference rules *)
(* ************************************************************************ *)

(* Equality resolution, alias ER *)
let equality_resolution p_set clause acc =
  if not p_set.rules.er then acc
  else do_resolution ~section:p_set.section acc clause

(* Supperposition rules, alias SN & SP
   Given a new clause, and the current set of clauses, there are two cases:
   - either the new clause might be the active clause in a SN or SP rule
     (i.e. the equality used to substitute)
   - or it is the inactive clause (i.e. the clause the substitution is
     performed on)
*)
let superposition rules acc u active inactive =
  if ((is_eq inactive.clause && rules.sp)
      || (* not is_eq && *) rules.sn) then
    do_supp acc u active inactive
  else
    acc

let add_passive_supp p_set clause side acc path = function
  | { Expr.term = Expr.Var _ }
  | { Expr.term = Expr.Meta _ } -> acc
  | p ->
    let l = I.find_unify p p_set.root_pos_index in
    let inactive = { clause; side; path } in
    List.fold_left (fun acc (_, u, l) ->
        List.fold_left (fun acc active ->
            superposition p_set.rules acc u active inactive
          ) acc l
      ) acc l

let add_active_supp p_set clause side s acc =
  let l = I.find_unify s p_set.inactive_index in
  let active = { clause; side; path = Position.root } in
  List.fold_left (fun acc (t, u, l) ->
      match t with
      | { Expr.term = Expr.Meta _ } -> acc
      | _ -> List.fold_left (fun acc inactive ->
          superposition p_set.rules acc u active inactive
        ) acc l
    ) acc l

(* Given a new clause, find and apply all instances of SN & SP,
   using the two functions defined above. *)
let supp_lit c p_set acc =
  match c.lit with
  | Empty -> acc
  | Eq (a, b) ->
    begin match Lpo.compare a b with
      | Comparison.Gt ->
        add_active_supp p_set c Left a
          (Position.Term.fold (add_passive_supp p_set c Left) acc a)
      | Comparison.Lt ->
        add_active_supp p_set c Right b
          (Position.Term.fold (add_passive_supp p_set c Right) acc b)
      | Comparison.Incomparable ->
        add_active_supp p_set c Left a
          (add_active_supp p_set c Right b
             (Position.Term.fold (add_passive_supp p_set c Left)
                (Position.Term.fold (add_passive_supp p_set c Right) acc b) a))
      | Comparison.Eq -> assert false (* trivial clauses should have been filtered *)
    end
  | Neq (a, b) ->
    begin match Lpo.compare a b with
      | Comparison.Gt ->
        Position.Term.fold (add_passive_supp p_set c Left) acc a
      | Comparison.Lt ->
        Position.Term.fold (add_passive_supp p_set c Right) acc b
      | Comparison.Incomparable ->
        Position.Term.fold (add_passive_supp p_set c Left)
          (Position.Term.fold (add_passive_supp p_set c Right) acc b) a
      | Comparison.Eq -> acc
    end

(* Rewriting of litterals, i.e RP & RN
   Since RP & RN are simplification rules, using the discount loop,
   we only have to mplement that inactive side of the rules.
   Indeed the discount loop will only ask us to simplify a given
   clause using a set of clauses, so given a clause to simplify,
   we only have to find all active clauses that can be used to
   simplify it.

   Here, given a term [u] (together with its [side] and [path]
   inside [clause]), we want to find an instance of a clause
   in [p_set] that might be used to rewrite [u]
*)
let rewrite rules active inactive =
  if ((is_eq inactive.clause && rules.rp)
      || (* not is_eq && *) rules.rn) then
    do_rewrite active inactive
  else
    None

let add_inactive_rewrite p_set clause side path u =
  let l = I.find_equal u p_set.root_pos_index in
  let inactive = { clause; side; path } in
  CCList.find_map (fun (_, l') ->
      CCList.find_map (fun active ->
          rewrite p_set.rules active inactive) l') l

(* Simplification function using the rules RN & RP. Returns
   [Some c'] if the clause can be simplified into a clause [c'],
   [None] otherwise. *)
let rewrite_lit p_set c =
  match c.lit with
  | Empty -> None
  | Eq (s, t) | Neq (s, t) ->
    let res = Position.Term.find_map (add_inactive_rewrite p_set c Left) s in
    begin match res with
      | Some _ -> res
      | None -> Position.Term.find_map (add_inactive_rewrite p_set c Right) t
    end

(* Squality_subsumption, alias ES
   Simalarly than above, we only want to check wether a given clause is redundant
   with regards to a set of clauses. Returns [true] if the given clause is redundant
   (i.e. can be simplified using the ES rule), [false] otherwise.
*)
let equality_subsumption c p_set =
  match c.lit with
  | Empty | Neq _ -> false
  | Eq (a, b) ->
    begin match make_eq p_set a b with
      | `Equal -> assert false (* trivial clause should have been eliminated *)
      | `Impossible -> false
      | `Substitutable (pos, l) ->
        p_set.rules.es && List.exists (fun x -> x.clause.map << c.map) l
    end

(* Main functions *)
(* ************************************************************************ *)

let rec fix f arg =
  match f arg with
  | None -> arg
  | Some y -> fix f y

(* Applies: RP, RN  *)
let simplify c p =
  fix (rewrite_lit p) c

(* Applies: RP, RN *)
let cheap_simplify = simplify

(* Applies: ES *)
let redundant c p =
  equality_subsumption c p

(* Applies: ER, SP, SN *)
let generate c p =
  supp_lit c p (equality_resolution p c [])

(* Applies: TD1 *)
let trivial c p =
  match c.lit with
  | Eq (a, b) when Expr.Term.equal a b -> true
  | _ -> S.mem c p.clauses

(* Enqueue a new clause in p *)
let enqueue c p =
  if S.mem c p.generated then p
  else begin
    let generated = S.add c p.generated in
    let c' = cheap_simplify c p in
    (* If claus has changed, print the original *)
    if not (c == c') then
      Util.debug ~section:p.section " |~ %a" pp c;
    (* Test triviality of the clause. Second test is against
       p.generated (and not generated) because if c == c', then
       we'd have a problem. *)
    if trivial c' p || S.mem c' p.generated then begin
      Util.debug ~section:p.section " |- %a" pp c';
      { p with generated }
      (* The clause is interesting and we add it to generated
         as well as the queue. *)
    end else begin
      Util.debug ~section:p.section " |+ %a" pp c';
      let queue = Q.insert c' p.queue in
      let generated = S.add c' generated in
      { p with queue; generated; }
    end
  end


(* Main loop *)
(* ************************************************************************ *)

let rec discount_loop p_set =
  match Q.take p_set.queue with
  | None -> p_set
  | Some (u, cl) ->
    (* Simplify the clause to add *)
    let c = simplify cl p_set in
    if compare c cl <> 0 then
      Util.debug ~section:p_set.section "Original clause : %a" pp cl;
    (* If trivial or redundant, forget it and continue *)
    if trivial c p_set then begin
      Util.debug ~section:p_set.section "Trivial clause : %a" pp c;
      discount_loop { p_set with queue = u }
    end else if redundant c p_set then begin
      Util.debug ~section:p_set.section "Redundant clause : %a" pp c;
      discount_loop { p_set with queue = u }
    end else begin
      Util.debug ~section:p_set.section "@{<yellow>Adding clause@} : %a" pp c;
      if c.lit = Empty then begin
        Util.debug ~section:p_set.section
          "Empty clause reached, %d clauses in state" (S.cardinal p_set.clauses);
        (* Call the callback *)
        p_set.callback c.map;
        (* Continue solving *)
        discount_loop { p_set with queue = u }
      end else begin
        (* Add the clause to the set. *)
        let p_set = add_clause c p_set in
        (* Keep the clauses in the set inter-simplified *)
        let p_set, t = S.fold (fun p (p_set, t) ->
            let p_aux = rm_clause p p_set in
            let p' = simplify p p_aux in
            if p == p' then (* no simplification *)
              (p_set, t)
            else begin (* clause has been simplified, prepare to queue it back *)
              Util.debug ~section:p_set.section "@{<red>Removing@}: %a" pp p;
              (p_aux, S.add p' t)
            end) p_set.clauses (p_set, S.empty) in
        (* Generate new inferences *)
        let l = generate c p_set in
        Util.debug ~section:p_set.section "@{<green>Generated %d inferences@}" (List.length l);
        let t = List.fold_left (fun s p -> S.add p s) t l in
        (* Do a cheap simplify on the new clauses, and then add them to the queue. *)
        let p = S.fold enqueue t { p_set with queue = u } in
        discount_loop p
      end
    end

(* Wrappers/Helpers for unification *)
(* ************************************************************************ *)

let add_eq t a b =
  let c = mk_eq a b Unif.empty Hyp in
  enqueue c t

let add_neq t a b =
  let c = mk_neq a b Unif.empty Hyp in
  enqueue c t

let solve t =
  discount_loop t

