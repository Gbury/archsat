(*
   This module uses unitary supperposition to
   unify terms modulo equality.
   For a reference, see :
   'E, a brainiac theorem prover' by shulz.
*)

module C = Set.Make(Mapping)

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
  | Fresh of clause
  | ER of clause
  | ES of pointer * pointer
  | SN of pointer * pointer
  | SP of pointer * pointer
  | RN of pointer * pointer
  | RP of pointer * pointer
  | MN of pointer * pointer
  | MP of pointer * pointer

(* Type for unit clauses, i.e clauses with at most one equation *)
and clause = {
  id : int;                 (* Unique id (for printing and tracking through logs) *)
  lit : lit;                (* Contents of the clause *)
  map : C.t;                (* Current mapping for variables & meta-variables *)
  reason : reason;          (* Reason of the clause *)
  weight : int;             (* weight of the clause (clauses with lesser
                               weight are selected first) *)
}

and pointer = {
  clause : clause;
  side : side;
  path : Position.t;
}

(* Weight computing *)
(* ************************************************************************ *)

let rec term_size acc = function
  | { Expr.term = Expr.App (_, _, l) } ->
    List.fold_left term_size (acc + 1) l
  | _ -> acc + 1

(* Alpha-renaming *)
(* ************************************************************************ *)

let bind_leaf_ty _ ty acc =
  match ty with
  | { Expr.ty = Expr.TyApp _ } -> raise Exit
  | { Expr.ty = Expr.TyVar v } ->
    if Mapping.Var.mem_ty acc v then raise Exit
    else Mapping.Var.bind_ty acc v Expr.Ty.base
  | { Expr.ty = Expr.TyMeta m } ->
    if Mapping.Meta.mem_ty acc m then raise Exit
    else Mapping.Meta.bind_ty acc m Expr.Ty.base

let bind_leaf_term _ term acc =
  match term with
  | { Expr.term = Expr.App _ } -> raise Exit
  | { Expr.term = Expr.Var v } ->
    if Mapping.Var.mem_term acc v then raise Exit
    else Mapping.Var.bind_term acc v (Expr.Term.of_id v)
  | { Expr.term = Expr.Meta m } ->
    if Mapping.Meta.mem_term acc m then raise Exit
    else Mapping.Meta.bind_term acc m (Expr.Term.of_meta m)

let is_alpha m =
  try
    let _ = Mapping.fold
        ~ty_var:bind_leaf_ty
        ~ty_meta:bind_leaf_ty
        ~term_var:bind_leaf_term
        ~term_meta:bind_leaf_term
        m Mapping.empty
    in true
  with Exit -> false

(* Substitutions *)
(* ************************************************************************ *)

let simpl_mapping m =
  Mapping.filter
    ~ty_var:(fun v ty -> not @@ Expr.Ty.(equal ty @@ of_id v))
    ~ty_meta:(fun m ty -> not @@ Expr.Ty.(equal ty @@ of_meta m))
    ~term_var:(fun v term -> not @@ Expr.Term.(equal term @@ of_id v))
    ~term_meta:(fun m term -> not @@ Expr.Term.(equal term @@ of_meta m))
    m

(* can s be composed with another mapping to be equal/included in s' *)
let match_subst s s' =
  let aux get f_match x t acc =
    match get s' x with
    | t' -> f_match acc t t'
    | exception Not_found -> acc
  in
  let ty_var = aux Mapping.Var.get_ty Match.ty in
  let ty_meta = aux Mapping.Meta.get_ty Match.ty in
  let term_var = aux Mapping.Var.get_term Match.term in
  let term_meta = aux Mapping.Meta.get_term Match.term in
  Mapping.fold ~ty_var ~term_var ~ty_meta ~term_meta s Mapping.empty

let (<) s t =
  try
    let _ = match_subst s t in
    true
  with
  | Match.Impossible_ty _
  | Match.Impossible_term _ -> false

let (<<) t t' =
  C.for_all (fun s' -> C.exists (fun s -> s < s') t) t'


(* Mapping composition *)

let compose s s' =
  Mapping.map
    (Mapping.apply_ty s')
    (Mapping.apply_term s') s

let compose_set set rho =
  C.map (fun s -> compose s rho) set


(* Mapping merging *)

let merge_aux s s' =
  let aux get f_match x t acc =
    match get s' x with
    | t' -> f_match acc t t'
    | exception Not_found -> acc
  in
  let ty_var = aux Mapping.Var.get_ty Unif.Robinson.ty in
  let ty_meta = aux Mapping.Meta.get_ty Unif.Robinson.ty in
  let term_var = aux Mapping.Var.get_term Unif.Robinson.term in
  let term_meta = aux Mapping.Meta.get_term Unif.Robinson.term in
  Mapping.fold ~ty_var ~term_var ~ty_meta ~term_meta s Mapping.empty

let merge s s' =
  match merge_aux s s' with
  | exception Unif.Robinson.Impossible_ty _ -> None
  | exception Unif.Robinson.Impossible_term _ -> None
  | rho ->
    let aux ~eq ~f = function
      | None, None -> assert false
      | Some x, None
      | None, Some x -> Some (f x)
      | Some x, Some y ->
        let x' = f x in
        let y' = f y in
        assert (eq x' y');
        Some x'
    in
    let aux_ty _ opt opt' =
      aux ~eq:Expr.Ty.equal ~f:(Mapping.apply_ty rho) (opt, opt') in
    let aux_term _ opt opt' =
      aux ~eq:Expr.Term.equal ~f:(Mapping.apply_term rho) (opt, opt') in
    Some (Mapping.merge
            ~ty_var:aux_ty ~ty_meta:aux_ty
            ~term_var:aux_term ~term_meta:aux_term
            s s')

let merge_set set set' =
  C.fold (fun s acc ->
      C.fold (fun s' acc' ->
          match merge s s' with
          | None -> acc'
          | Some s'' -> C.add s'' acc'
        ) set' acc) set C.empty

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
  | Empty, Empty -> C.compare c.map c'.map
  | Eq (a, b), Eq (a', b')
  | Neq (a, b), Neq (a', b') ->
    CCOrd.(Expr.Term.compare a a'
           <?> (Expr.Term.compare, b, b')
           <?> (C.compare, c.map, c'.map))
  | x, y -> Pervasives.compare (_discr x) (_discr y)

(* Printing of clauses *)
let rec pp_id fmt c =
  match c.reason with
  | Fresh c' -> Format.fprintf fmt "~%a" pp_id c'
  | _ -> Format.fprintf fmt "C%d" c.id

let pp_pos fmt pos =
  let dir = if pos.side = Left then "→" else "←" in
  Format.fprintf fmt "%a%s%a" pp_id pos.clause dir Position.print pos.path

let pp_reason fmt c =
  match c.reason with
  | Hyp -> Format.fprintf fmt "hyp"
  | Fresh c -> Format.fprintf fmt "Fresh(%a)" pp_id c
  | ER d -> Format.fprintf fmt "ER(%a)" pp_id d
  | SN (d, e) -> Format.fprintf fmt "SN(%a;%a)" pp_pos d pp_pos e
  | SP (d, e) -> Format.fprintf fmt "SP(%a;%a)" pp_pos d pp_pos e
  | ES (d, e) -> Format.fprintf fmt "ES(%a;%a)" pp_pos d pp_pos e
  | RN (d, e) -> Format.fprintf fmt "RN(%a;%a)" pp_pos d pp_pos e
  | RP (d, e) -> Format.fprintf fmt "RP(%a;%a)" pp_pos d pp_pos e
  | MN (d, e) -> Format.fprintf fmt "MN(%a;%a)" pp_pos d pp_pos e
  | MP (d, e) -> Format.fprintf fmt "MP(%a;%a)" pp_pos d pp_pos e

let pp_cmp ~pos fmt (a, b) =
  let s = Comparison.to_string (Lpo.compare a b) in
  let s' =
    if pos then s
    else CCString.flat_map (function
          | '=' -> "≠" | c -> CCString.of_char c) s
  in
  Format.fprintf fmt "%s" s'

let pp_lit fmt c =
  match c.lit with
  | Empty -> Format.fprintf fmt "∅"
  | Eq (a, b) ->
    Format.fprintf fmt "@[%a@ %a@ %a@]"
      Expr.Print.term a (pp_cmp ~pos:true) (a, b) Expr.Print.term b
  | Neq (a, b) ->
    Format.fprintf fmt "@[%a@ %a@ %a@]"
      Expr.Print.term a (pp_cmp ~pos:false) (a, b) Expr.Print.term b

let pp_map fmt c =
  C.iter (fun m -> Format.fprintf fmt "@,[%a]" Mapping.print m) c.map

let pp fmt (c:clause) =
  Format.fprintf fmt "@[<hov 2>%a@,[%a]@,[%a]%a@]"
    pp_id c pp_reason c pp_lit c pp_map c

(* Heuristics for clauses. Currently uses the size of terms.
   NOTE: currently, weight does not take the subst into account so that
         clauses that might be merged have the same weight and thus are
         added together.
   TODO: merge clauses in the queue ?
   TODO: better heuristic for clause selection.
*)
let compute_weight = function
  | Empty -> 0
  | Eq (a, b) -> 2 * (term_size (term_size 0 b) a)
  | Neq (a, b) -> 1 * (term_size (term_size 0 b) a)
  (* Disequalities have smaller weight because we are more interested
     in them (better chance to apply rule ER, and get a solution) *)

let leq_cl c c' =
  c.weight <= c'.weight || (
    c.weight = c'.weight &&
    C.cardinal c.map >= C.cardinal c'.map
  )

(* Clauses *)
let mk_cl =
  let i = ref 0 in
  (fun lit map reason ->
     incr i;
     let weight = compute_weight lit in
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

(* Clause freshening *)
(* ************************************************************************ *)

let fresh a b map =
  assert (Expr.Term.fm a = ([], []));
  assert (Expr.Term.fm b = ([], []));
  let tys, terms = Expr.Id.merge_fv (Expr.Term.fv a) (Expr.Term.fv b) in
  let vtys = List.map (fun v -> Expr.Id.ttype "v") tys in
  let vterms = List.map (fun v -> Expr.Id.ty "v" Expr.(v.id_type)) terms in
  let m =
    List.fold_left2 (fun acc m v ->
        Mapping.Var.bind_ty acc m (Expr.Ty.of_id v)) (
      List.fold_left2 (fun acc m v ->
          Mapping.Var.bind_term acc m (Expr.Term.of_id v))
        Mapping.empty terms vterms) tys vtys in
  (Mapping.apply_term m a), (Mapping.apply_term m b), (compose_set map m)

let freshen c =
  match c.lit with
  | Empty -> c
  | Eq (a, b)
  | Neq (a, b) ->
    let f = if is_eq c then mk_eq else mk_neq in
    let a', b', m' = fresh a b c.map in
    f a' b' m' (Fresh c)

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
(*
module Q = CCHeap.Make(struct type t = clause let leq = leq_cl end)
*)
module Q = struct

  type t = {
    top : clause list;
    bot : clause list;
  }

  let empty = {
    top = [];
    bot = [];
  }

  let fold f acc q =
    let acc' = List.fold_left f acc q.top in
    List.fold_left f acc' q.bot

  let insert c q =
    { q with bot = c :: q.bot }

  let rec take q =
    match q.top with
    | x :: r -> Some ({q with top = r }, x)
    | [] ->
      begin match q.bot with
        | [] -> None
        | l -> take { top = List.rev l; bot = [] }
      end

end
module S = Set.Make(struct type t = clause let compare = compare end)
module I = Index.Make(struct type t = pointer let compare = compare_pointer end)

type rules = {
  er : bool;
  es : bool;
  sn : bool;
  sp : bool;
  rn : bool;
  rp : bool;
  mn : bool;
  mp : bool;
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
  callback : (Mapping.t -> unit);
}

let all_rules = {
  er = true;
  es = true;
  sn = true;
  sp = true;
  rp = true;
  rn = true;
  mn = true;
  mp = true;
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

(* Symbol precedence *)
(* ************************************************************************ *)

module Symbols = Set.Make(Expr.Id.Const)

let rec term_symbols acc = function
  | { Expr.term = Expr.Var _ }
  | { Expr.term = Expr.Meta _ } -> acc
  | { Expr.term = Expr.App (f, _, l) } ->
    List.fold_left term_symbols (Symbols.add f acc) l

let clause_symbols acc c =
  match c.lit with
  | Empty -> acc
  | Eq (a, b) | Neq (a, b) ->
    term_symbols (term_symbols acc a) b

let set_symbols t =
  let s = Symbols.empty in
  let s' = Q.fold clause_symbols s t.queue in
  S.fold (CCFun.flip clause_symbols) t.clauses s'

let pp_precedence fmt t =
  let s = set_symbols t in
  let l = Symbols.elements s in
  let sep fmt () = Format.fprintf fmt " <@ " in
  CCFormat.list ~sep Expr.Id.Const.print fmt l

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
    begin match Unif.Robinson.term Mapping.empty s t with
      | mgu -> mk_empty (compose_set sigma mgu) clause :: acc
      | exception Unif.Robinson.Impossible_ty _ -> acc
      | exception Unif.Robinson.Impossible_term _ -> acc
    end

(* Perform a superposition, i.e either rule SN or SP
   [active] is (the position of) the equality used to perform the substitution,
   [inactive] is (the position of) the clause the substitution is being performed on
   [mgu] is the subtitution that unifies [active] and [inactive]
   TODO: check the LPO constraints iff it really need to be checked
         i.e. only when the ordering failed on the non-instanciated clause
*)
let do_supp acc sigma'' active inactive =
  assert (is_eq active.clause);
  assert (Position.equal active.path Position.root);
  let p = inactive.path in
  let s, t = extract active in
  let u, v = extract inactive in
  let sigma = active.clause.map in
  let sigma' = inactive.clause.map in
  (* Merge the substitutions. *)
  let res = merge_set (compose_set sigma sigma'') (compose_set sigma' sigma'') in
  let apply = Mapping.apply_term sigma'' in
  let v' = apply v in
  let u_res, u_p_opt = Position.Term.apply p u in
  (* Chekc that mgu effectively unifies u_p and s *)
  assert (match u_p_opt with
      | None -> false
      | Some u_p ->
        Expr.Term.equal (apply s) (apply u_p));
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
      let u'', v'', map = fresh u' v' res in
      let c = f u'' v'' map reason in
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
  assert (Position.equal active.path Position.root);
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
      let u'', v', map = fresh u' v sigma in
      Some (f u'' v' map reason)
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

(* Perform equality subsumption *)
let do_subsumption active inactive =
  assert (is_eq active.clause);
  assert (is_eq inactive.clause);
  assert (Position.equal Position.root active.path);
  let sigma = active.clause.map in
  let s, t = extract active in
  let u, v = extract inactive in
  assert (
    match Position.Term.apply inactive.path u with
    | _, Some (u_p) -> Expr.Term.equal u_p s
    | _, None -> false
  );
  assert (
    match Position.Term.substitute inactive.path ~by:t u with
    | Some u' -> Expr.Term.equal u' v
    | None -> false
  );
  let redundant, sigma' = C.partition (fun rho ->
      C.exists (fun s -> s < rho) sigma) inactive.clause.map in
  if C.is_empty redundant then
    inactive.clause
  else
    mk_eq u v sigma' (ES (active, inactive))

(* Perform clause merging *)
let do_merging p active inactive rho =
  assert ((is_eq active.clause && is_eq inactive.clause) ||
          (not @@ is_eq active.clause && not @@ is_eq inactive.clause));
  let sigma = active.clause.map in
  let sigma' = inactive.clause.map in
  let s, t = extract active in
  let u, v = extract inactive in
  assert (Expr.Term.equal (Mapping.apply_term ~fix:false rho u) s);
  assert (Expr.Term.equal (Mapping.apply_term ~fix:false rho v) t);
  if is_alpha rho then begin
    let f = if is_eq inactive.clause then mk_eq else mk_neq in
    let reason =
      if is_eq inactive.clause
      then MP (active, inactive)
      else MN (active, inactive)
    in
    let c = C.union sigma (compose_set sigma' rho) in
    Util.debug ~section:p.section "@{<Red>Removing@}: %a" pp active.clause;
    Some (rm_clause active.clause p, f s t c reason)
  end else None


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
  let c = freshen c in
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
   we only have to implement that inactive side of the rules.
   Indeed the discount loop will only ask us to simplify a given
   clause using a set of clauses, so given a clause to simplify,
   we only have to find all active clauses that can be used to
   simplify it.

   Here, given a term [u] (together with its [side] and [path]
   inside [clause]), we want to find an instance of a clause
   in [p_set] that might be used to rewrite [u]
*)
let rewrite p active inactive =
  if ((is_eq inactive.clause && p.rules.rp) ||
      (not @@ is_eq inactive.clause && p.rules.rn)) then
    CCOpt.map (fun x -> p, x) @@ do_rewrite active inactive
  else
    None

let add_inactive_rewrite p_set clause side path u =
  let l = I.find_equal u p_set.root_pos_index in
  let inactive = { clause; side; path } in
  CCList.find_map (fun (_, l') ->
      CCList.find_map (fun active ->
          rewrite p_set active inactive) l') l

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

(* Equality_subsumption, alias ES
   Simalarly than above, we only want to check wether a given clause is redundant
   with regards to a set of clauses. Returns [true] if the given clause is redundant
   (i.e. can be simplified using the ES rule), [false] otherwise.
*)
let equality_subsumption p_set c =
  if not p_set.rules.es then None
  else match c.lit with
  | Empty | Neq _ -> None
  | Eq (a, b) ->
    begin match make_eq p_set a b with
      | `Equal -> assert false (* trivial clause should have been eliminated *)
      | `Impossible -> None
      | `Substitutable (path, l) ->
        let aux clause pointer =
          do_subsumption pointer { clause; path; side = Left;}
        in
        let c' = List.fold_left aux c l in
        if c == c' then None else Some (p_set, c')
    end

let merge_aux p active inactive mgm =
  let s, t = extract active in
  let u, v = extract inactive in
  assert (Expr.Term.equal (Mapping.apply_term ~fix:false mgm u) s);
  match Match.term mgm v t with
  | alpha -> do_merging p active inactive (simpl_mapping alpha)
  | exception Match.Impossible_ty _ -> None
  | exception Match.Impossible_term _ -> None

let merge_sided p clause side x index =
  let inactive = { clause; path = Position.root; side; } in
  let l = I.find_match x index in
  CCList.find_map (fun (_, mgm, l') ->
      CCList.find_map (fun active ->
          merge_aux p active inactive mgm
        ) l') l

let merge p_set clause =
  let index = if is_eq clause then p_set.root_pos_index else p_set.root_neg_index in
  match clause.lit with
  | Empty -> None
  | Eq (a, b)
  | Neq (a, b) ->
    begin match merge_sided p_set clause Left a index with
      | (Some _) as res -> res
      | None -> merge_sided p_set clause Right b index
    end

(* Main functions *)
(* ************************************************************************ *)

(* Applies: TD1, TD2 *)
let trivial c p =
  match c.lit with
  | Eq (a, b) when Expr.Term.equal a b -> true  (* TD1 *)
  | _ when C.is_empty c.map -> true             (* TD2 *)
  | _ -> S.mem c p.clauses                      (* Simple redundancy criterion *)

(* Fixpoint for simplification rules *)
let rec fix f p clause =
  if trivial clause p then p, clause
  else match f p clause with
    | None -> p, clause
    | Some (p', clause') ->
      Util.debug ~section:p.section "(simpl) %a" pp clause';
      fix f p' clause'

let (|>>) f g = fun p x ->
  match f p x with
  | None -> g p x
  | (Some _) as res -> res

(* Applies: ES, RP, RN *)
let simplify c p =
  let aux = equality_subsumption |>>
            merge |>> rewrite_lit in
  fix aux p c

(* Applies: ES, RP, RN *)
let cheap_simplify c p =
  let aux = equality_subsumption |>> rewrite_lit in
  snd (fix aux p c)

(* Applies: ER, SP, SN *)
let generate c p =
  supp_lit c p (equality_resolution p c [])

(* Enqueue a new clause in p *)
let enqueue c p =
  if S.mem c p.generated then p
  else begin
    let generated = S.add c p.generated in
    let c' = cheap_simplify c p in
    if not (c == c') then
      (* If clause has changed, print the original *)
      Util.debug ~section:p.section " |~ %a" pp c;
    (* Test triviality of the clause. Second test is against
       p.generated (and not generated) because if c == c', then
       we'd have a problem. *)
    if trivial c' p || S.mem c' p.generated then begin
      Util.debug ~section:p.section " |- %a" pp c';
      { p with generated }
    end else begin
      (* The clause is interesting and we add it to generated
         as well as the queue. *)
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
    Util.debug ~section:p_set.section "Simplifying: @[<hov>%a@]" pp cl;
    let p_set, c = simplify cl p_set in
    (* If trivial or redundant, forget it and continue *)
    if trivial c p_set then begin
      Util.debug ~section:p_set.section "Trivial clause : %a" pp c;
      discount_loop { p_set with queue = u }
    end else begin
      Util.debug ~section:p_set.section "@{<yellow>Adding clause@} : %a" pp c;
      if c.lit = Empty then begin
        Util.debug ~section:p_set.section
          "Empty clause reached, %d clauses in state" (S.cardinal p_set.clauses);
        (* Call the callback *)
        C.iter p_set.callback c.map;
        (* Continue solving *)
        discount_loop { p_set with queue = u }
      end else begin
        (* Add the clause to the set. *)
        let p_set = add_clause c p_set in
        (* Keep the clauses in the set inter-simplified *)
        let p_set, t = S.fold (fun p (p_set, t) ->
            let p_aux = rm_clause p p_set in
            let p_set', p' = simplify p p_aux in
            if p == p' then (* no simplification *)
              (p_set, t)
            else begin (* clause has been simplified, prepare to queue it back *)
              Util.debug ~section:p_set.section "@{<Red>Removing@}: %a" pp p;
              (p_set', S.add p' t)
            end) p_set.clauses (p_set, S.empty) in
        (* Generate new inferences *)
        let l = generate c p_set in
        Util.debug ~section:p_set.section "@{<green>Generated %d (%d) inferences@}"
          (List.length l) (S.cardinal t);
        let t = List.fold_left (fun s p -> S.add p s) t l in
        (* Do a cheap simplify on the new clauses, and then add them to the queue. *)
        let p = S.fold enqueue t { p_set with queue = u } in
        discount_loop p
      end
    end

(* Wrappers/Helpers for unification *)
(* ************************************************************************ *)

let meta_to_var a b =
  assert (Expr.Term.fv a = ([], []));
  assert (Expr.Term.fv b = ([], []));
  let tys, terms = Expr.Meta.merge_fm (Expr.Term.fm a) (Expr.Term.fm b) in
  let vtys = List.map (fun m -> Expr.Id.ttype "v") tys in
  let vterms = List.map (fun m -> Expr.Id.ty "v" Expr.(m.meta_id.id_type)) terms in
  let m =
    List.fold_left2 (fun acc m v ->
        Mapping.Meta.bind_ty acc m (Expr.Ty.of_id v)) (
      List.fold_left2 (fun acc m v ->
          Mapping.Meta.bind_term acc m (Expr.Term.of_id v))
        Mapping.empty terms vterms) tys vtys in
  Mapping.apply_term m a, Mapping.apply_term m b, m

let add_eq t a b =
  let a', b', m = meta_to_var a b in
  let c = mk_eq a' b' (C.singleton m) Hyp in
  enqueue c t

let add_neq t a b =
  let a', b', m = meta_to_var a b in
  let c = mk_neq a' b' (C.singleton m) Hyp in
  enqueue c t

let solve t =
  Util.debug ~section:t.section "@{<White>Precedence@}: @[<hov>%a@]" pp_precedence t;
  let rules = t.rules in
  (* Pre-saturate hyps so that they merge together *)
  Util.debug ~section:t.section "@{<White>Preparing solver@}: merging hypotheses";
  let t' = { t with rules = { rules with er = false; sn = false; sp = false; } } in
  let t'' = discount_loop t' in
  (* Take the merge hyps and begin solving for real *)
  Util.debug ~section:t.section "@{<White>Beginning solving@}";
  let f = empty ~rules t.section t.callback in
  let f' = S.fold enqueue t''.clauses f in
  discount_loop f'

