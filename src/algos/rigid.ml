(*
   This module implements rigid unification modulo
   equality as described in :
   'Implementing Rigid E-unification', by Michael Franssen
   [http://gbury.eu/public/rigid.pdf]
*)

(*
let log_section = Util.Section.make "rigid"
let log i fmt = Util.debug ~section:log_section i fmt
*)

(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)
module H = Hashtbl.Make(Expr.Term)
module U = Map.Make(Unif)

module G = Graph.Persistent.Digraph.Concrete(Expr.Term)
module T = Graph.Traverse.Dfs(G)

module P = CCPersistentArray

type term = Expr.Term.t

type graph = {
  graph : G.t;
  incoming : int M.t;
}

type simple_system =
  | Empty (* () *)
  | Equal of term * simple_system (* t = ... *)
  | Greater of term * simple_system (* t > ... *)

type solved_form = {
  solved : Unif.t;
  constraints : (term * term) list; (* t < t' *)
}

type solved_form_list = (term * term) list list U.t

type rule =
  | RRBS
  | LRBS

type problem = {
  depth: int;
  max_depth: int;
  eqs : (term * term) P.t;
  last_rule : rule;
  goal : term * term;
  lrbs_index : int;
  constr : solved_form_list;
}

(* Printing *)
(* ************************************************************************ *)
(*
let rec debug_ss b = function
  | Empty -> Printf.bprintf b "."
  | Equal(t, Empty) | Greater (t, Empty) ->
    Printf.bprintf b "%a" Expr.Debug.term t
  | Equal (t, s) -> Printf.bprintf b "%a = %a" Expr.Debug.term t debug_ss s
  | Greater (t, s) -> Printf.bprintf b "%a > %a" Expr.Debug.term t debug_ss s
*)
(* Exceptions *)
(* ************************************************************************ *)

exception Sat_solved_form of simple_system (** NOT exported *)
exception Unsat_solved_form (** NOT exported *)

(* Solved forms misc *)
(* ************************************************************************ *)

let compare_constr (a, b) (a', b') =
  match Expr.Term.compare a a' with
  | 0 -> Expr.Term.compare b b'
  | x -> x

let compare_cl = CCOrd.list_ compare_constr

let sf_add_lt sf s t = (* Add s < t to sf *)
  { sf with
    constraints = CCList.sorted_merge_uniq ~cmp:compare_constr sf.constraints [(s, t)]
  }

(* Solved forms list as map from solved to contraints. *)
let empty_sf_list = U.empty
let sf_singleton sf = U.singleton sf.solved [sf.constraints]

let sf_merge m m' =
  U.merge (fun solved v v' -> match v, v' with
      | Some l, None | None, Some l -> Some l
      | Some l, Some l' -> Some (CCList.sorted_merge_uniq ~cmp:compare_cl l l')
      | None, None -> assert false) m m'

let sf_filter f m =
  U.fold (fun u l acc -> match List.filter f l with
        [] -> acc | l' -> U.add u l' acc) empty_sf_list m

let sf_fold f acc m =
  U.fold (fun solved l acc' ->
      List.fold_left (fun acc'' constraints ->
          f { solved; constraints } acc'')
        acc' l)
    m acc

let sf_is_empty m = U.is_empty m

(* Checking simple systems *)
(* ************************************************************************ *)

let length s =
  let rec aux acc = function
    | Empty -> acc
    | Equal (_, s) | Greater (_, s) -> aux (acc + 1) s
  in
  aux 0 s

(* Deduce ordering directly implied by a simple system *)
let rec ss_appears t strict = function
  | Empty -> None
  | Equal (t', s) | Greater (t', s) when Expr.Term.equal t t' ->
    Some strict
  | Equal (_, s) -> ss_appears t strict s
  | Greater (_, s) -> ss_appears t true s

let rec ss_compare_aux t t' = function
  | Empty -> Comparison.Incomparable
  | Equal (t'', s) when Expr.Term.equal t t'' ->
    begin match ss_appears t' false s with
      | None -> Comparison.Incomparable
      | Some true -> Comparison.Gt
      | Some false -> Comparison.Eq
    end
  | Equal (t'', s) when Expr.Term.equal t' t'' ->
    begin match ss_appears t' false s with
      | None -> Comparison.Incomparable
      | Some true -> Comparison.Lt
      | Some false -> Comparison.Eq
    end
  | Greater (t'', s) when Expr.Term.equal t t'' ->
    begin match ss_appears t' true s with
      | None -> Comparison.Incomparable
      | Some true -> Comparison.Gt
      | Some false -> assert false
    end
  | Greater (t'', s) when Expr.Term.equal t' t'' ->
    begin match ss_appears t' true s with
      | None -> Comparison.Incomparable
      | Some true -> Comparison.Lt
      | Some false -> assert false
    end
  | Equal (_, s) | Greater (_, s) -> ss_compare_aux t t' s

let ss_compare s t t' =
  if Expr.Term.equal t t' then
    Comparison.Eq
  else
    ss_compare_aux t t' s

let ss_equal s t t' = ss_compare s t t' = Comparison.Eq
let ss_greatereq s t t' = match ss_compare s t t' with
  | Comparison.Gt | Comparison.Eq -> true | _ -> false

let rec ss_greater_lexico s l l' = match l, l' with
  | t :: r, t' :: r' -> begin match ss_compare s t t' with
      | Comparison.Eq -> ss_greater_lexico s r r'
      | cmp -> cmp
    end
  | _ -> Comparison.Incomparable

(* Check coherence of a simple system *)
let check_greater_aux s t t' = match t, t' with
  | { Expr.term = Expr.App (f, _, f_args) }, { Expr.term = Expr.App (g, _, g_args) } ->
    if Expr.Id.compare f g < 0 then
      List.exists (fun arg -> ss_greatereq s arg t') f_args
    else
      ss_greater_lexico s f_args g_args = Comparison.Gt
  | _ -> true

let rec check_greater t = function
  | Empty -> true
  | Equal (t', s) | Greater (t', s) ->
    check_greater_aux s t t' && check_greater t s

let check_equal_aux s t t' = match t, t' with
  | { Expr.term = Expr.App (f, _, f_args) }, { Expr.term = Expr.App (g, _, g_args) } ->
    if not (Expr.Id.equal f g) then false
    else List.for_all2 (ss_equal s) f_args g_args
  | _ -> true

let rec check_equal t = function
  | Empty -> true
  | Greater (t', s) -> check_equal_aux s t t' && check_greater t s
  | Equal (t', s) -> check_equal_aux s t t' && check_equal t s

let valid_ss = function
  | Empty -> true
  | Greater (t, s) -> check_greater t s
  | Equal (t, s) -> check_equal t s

(* Simple systems from solved forms *)
(* ************************************************************************ *)

let empty_graph = {
  graph = G.empty;
  incoming = M.empty;
}

let get_in g v = try M.find v g.incoming with Not_found -> 0
let incr_in g v = { g with incoming = M.add v (get_in g v + 1) g.incoming }
let decr_in g v = { g with incoming = M.add v (get_in g v - 1) g.incoming }

let rec subterms = function
  | { Expr.term = Expr.App (f, _, l) } as t -> t :: CCList.flat_map subterms l
  | t -> [t]

let add_edge g t t' = incr_in { g with graph = G.add_edge g.graph t t' } t'

let add_vertex g v = G.fold_vertex
    (fun t g -> if Lpo.compare t v = Comparison.Lt then add_edge g t v else g)
    g.graph { g with graph = G.add_vertex g.graph v }

let graph c =
  let l = CCList.flat_map (fun (t, t') -> List.rev_append (subterms t) (subterms t')) c in
  let l = List.sort_uniq Expr.Term.compare l in
  let l = List.sort (fun t t' -> Comparison.to_total (Lpo.compare t t')) l in
  let g = List.fold_left add_vertex empty_graph l in
  let g = List.fold_left (fun g (t, t') -> add_edge g t t') g c in
  if T.has_cycle g.graph then raise Unsat_solved_form
  else g

let get_level levels v = try H.find levels v with Not_found -> 0
let incr_level levels v = H.replace levels v (get_level levels v + 1)

let rec find_ss g levels lvl s =
  if length s = G.nb_vertex g.graph then raise (Sat_solved_form s)
  else begin
    G.iter_vertex (fun v ->
        if get_in g v = 0 then begin
          let g = decr_in g v in
          let g = G.fold_succ (fun v' g' -> incr_level levels v'; decr_in g' v') g.graph v g in
          if lvl >= get_level levels v && valid_ss (Equal (v, s)) then
            find_ss g levels lvl (Equal (v, s));
          if valid_ss (Greater (v, s)) && length s > 0 then
            find_ss g levels (lvl + 1) (Greater (v, s));
        end
      ) g.graph
  end

let valid_sf constrs =
  try
    let levels = H.create 64 in
    find_ss (graph constrs) levels 0 Empty;
    false
  with
  | Unsat_solved_form -> false
  | Sat_solved_form _ -> true

let sf_set_sat = sf_filter valid_sf

(* Computing solved forms *)
(* ************************************************************************ *)

let sf_empty = {
  solved = Unif.empty;
  constraints = [];
}

let sf_belongs sf (s, t) =
  List.exists (fun (s', t') ->
      Expr.Term.equal s s' && Expr.Term.equal t t') sf.constraints

let rec add_eq sf s t =
  let s = Unif.follow_term sf.solved s in
  let t = Unif.follow_term sf.solved t in
  match s, t with
  | _ when Expr.Term.equal s t -> sf_singleton sf
  | ({ Expr.term = Expr.Meta m}), w
  | w, ({ Expr.term = Expr.Meta m}) ->
    if Unif.occurs_term sf.solved [m] w then empty_sf_list
    else add_subst sf m w
  | { Expr.term = Expr.App (f, f_ty_args, f_args) },
    { Expr.term = Expr.App(g, g_ty_args, g_args) } ->
    if Expr.Id.compare f g = 0 then begin
      try
        let u = List.fold_left2 Unif.Robinson.ty
            sf.solved f_ty_args g_ty_args in
        List.fold_left2 add_eq_set (sf_singleton {sf with solved = u}) f_args g_args
      with Unif.Robinson.Impossible_ty _ ->
        empty_sf_list
    end else
      empty_sf_list
  | { Expr.term = Expr.Var _ }, _
  | _, { Expr.term = Expr.Var _ } ->
    assert false

and add_eq_set l s t =
  sf_set_sat (sf_fold (fun sf acc -> sf_merge acc (add_eq sf s t)) empty_sf_list l)

and add_subst sf m t =
  try
    let u = Unif.Robinson.ty sf.solved Expr.(m.meta_id.id_type) Expr.(t.t_type) in
    List.fold_left (fun acc (s, t) -> add_gt_set acc t s)
      (sf_singleton {solved = Unif.bind_term u m t; constraints = []}) sf.constraints
  with Unif.Robinson.Impossible_ty (ty, ty') ->
    empty_sf_list

and add_gt sf s t =
  let s = Unif.follow_term sf.solved s in
  let t = Unif.follow_term sf.solved t in
  match s, t with
  | { Expr.term = Expr.Meta m }, _
    when Unif.occurs_term sf.solved [m] t -> empty_sf_list
  | _, { Expr.term = Expr.Meta m }
    when Unif.occurs_term sf.solved [m] s -> sf_singleton sf
  | { Expr.term = Expr.Meta _ }, _ | _, { Expr.term = Expr.Meta _ }
    when sf_belongs sf (s, t) -> empty_sf_list
  | { Expr.term = Expr.Meta _ }, _ | _, { Expr.term = Expr.Meta _ } ->
    sf_singleton (sf_add_lt sf t s)
  | { Expr.term = Expr.App (f, _, f_args) },
    { Expr.term = Expr.App (g, _, g_args) } ->
    begin match Expr.Id.compare f g with
      | n when n > 0 ->
        List.fold_left (fun acc ti -> add_gt_set acc s ti) (sf_singleton sf) g_args
      | n when n < 0 ->
        List.fold_left (fun acc si -> sf_merge (sf_merge acc (add_eq sf si t)) (add_gt sf si t)) empty_sf_list f_args
      | _ (* f = g *) ->
        let base = List.fold_left (fun acc si -> sf_merge (sf_merge acc (add_eq sf si t)) (add_gt sf si t)) empty_sf_list f_args in
        let ssf = sf_singleton sf in
        let rec aux (res, eq) = function
          | [], [] -> res
          | si :: r, ti :: r' ->
            let h = add_gt_set eq si ti in
            let h = List.fold_left (fun h' tj -> add_gt_set h' s tj) h r' in
            aux (sf_merge res h, add_eq_set eq si ti) (r, r')
          | _ -> assert false
        in
        aux (base, ssf) (f_args, g_args)
    end
  | { Expr.term = Expr.Var _ }, _
  | _, { Expr.term = Expr.Var _ } ->
    assert false

and add_gt_set l s t =
  sf_set_sat (sf_fold (fun sf acc -> sf_merge acc (add_gt sf s t)) empty_sf_list l)

(* BSE Calculus *)
(* ************************************************************************ *)

let mk_pb n l u v = {
    depth = 0;
    max_depth = n;
    eqs = P.of_list l;
    goal = (u, v);
    last_rule = RRBS;
    lrbs_index = -1;
    constr = sf_singleton sf_empty;
  }

(* ER rule, simply try and unify the goals *)
let rec apply_er k pb =
  let (s, t) = pb.goal in
  let res = add_eq_set pb.constr s t in
  if sf_is_empty res then
    apply_rrbs k pb
  else if pb.depth < pb.max_depth then
    U.iter (fun solved _ -> k (Unif.fixpoint solved)) res

(* RRBS rule: use an equality from hypothesis to modify goal *)
and apply_rrbs k pb =
  if pb.depth < pb.max_depth then begin
    let (s, t) = pb.goal in
    rrbs_aux k pb s t;
    rrbs_aux k pb t s;
    apply_lrbs k pb
  end

and rrbs_aux k pb s t =
  let sat = add_gt_set pb.constr s t in
  if not (sf_is_empty sat) then begin
    let pb = { pb with constr = sat } in
    match pb.last_rule with
    | LRBS -> rrbs_index k pb s t (P.make 1 (P.get pb.eqs pb.lrbs_index))
    | RRBS -> rrbs_index k pb s t pb.eqs
  end

and rrbs_index k pb s t eqs =
  let subs = subterms s in
  for i = 0 to P.length eqs - 1 do
    let (l, r) = P.get eqs i in
    rrbs_eq_pre k pb s t l r subs;
    rrbs_eq_pre k pb s t r l subs;
  done

and rrbs_eq_pre k pb s t l r subs =
  let sat = add_gt_set pb.constr l r in
  if not (sf_is_empty sat) then begin
    let pb = { pb with constr = sat } in
    rrbs_eq k pb s t l r subs
  end

and rrbs_eq k pb s t l r = function
  | [] -> ()
  | { Expr.term = Expr.Meta _ } :: subs -> rrbs_eq k pb s t l r subs
  | p :: subs ->
    let sat = add_eq_set pb.constr l p in
    if not (sf_is_empty sat) then begin
      let s' = Expr.Term.replace (p,r) s in
      apply_er k { pb with last_rule = RRBS; constr = sat; goal = (s', t); depth = pb.depth + 1 }
    end;
    rrbs_eq k pb s t l r subs

(* Same as RRBS, but to modify another equality in hypothesis *)
and apply_lrbs k pb =
  if pb.lrbs_index < 0 then
    lrbs_jump_all k pb 0
  else
    lrbs_jump_lrbs k pb

and lrbs_jump_lrbs k pb =
  for j = 0 to P.length pb.eqs - 1 do
    lrbs_index k pb j pb.lrbs_index
  done;
  lrbs_jump_all k pb pb.lrbs_index

and lrbs_jump_all k pb start =
  for j = start to P.length pb.eqs - 1 do
    let s, t = P.get pb.eqs j in
    lrbs_jump_line k pb j s t;
    lrbs_jump_line k pb j t s
  done

and lrbs_jump_line k pb j s t =
  let sat = add_gt_set pb.constr s t in
  if not (sf_is_empty sat) then begin
    let pb = { pb with constr = sat } in
    for i = 0 to P.length pb.eqs - 1 do
      lrbs_jump_index_i k pb s t j i
    done
  end

and lrbs_jump_index_i k pb s t j i =
  let l, r = P.get pb.eqs i in
  let subs = subterms s in
  lrbs_eq_pre k pb j s t l r subs;
  lrbs_eq_pre k pb j s t r l subs

and lrbs_index k pb j i =
  let s, t = P.get pb.eqs j in
  let l, r = P.get pb.eqs i in
  lrbs_aux k pb j s t l r;
  lrbs_aux k pb j t s l r

and lrbs_aux k pb j s t l r =
  let sat = add_gt_set pb.constr s t in
  if not (sf_is_empty sat) then begin
    let pb = { pb with constr = sat } in
    let subs = subterms s in
    lrbs_eq_pre k pb j s t l r subs;
    lrbs_eq_pre k pb j s t r l subs
  end

and lrbs_eq_pre k pb j s t l r subs =
  let sat = add_gt_set pb.constr l r in
  if not (sf_is_empty sat) then
    lrbs_eq k { pb with constr = sat } j s t l r subs

and lrbs_eq k pb j s t l r = function
  | [] -> ()
  | { Expr.term = Expr.Meta _ } :: subs -> lrbs_eq k pb j s t l r subs
  | p :: subs ->
    let sat = add_eq_set pb.constr l p in
    if not (sf_is_empty sat) then begin
      let s' = Expr.Term.replace (p,r) s in
      apply_rrbs k { pb with last_rule = LRBS; lrbs_index = j; depth = pb.depth + 1;
                             constr = sat; eqs = P.set pb.eqs j (s',t) }
    end;
    lrbs_eq k pb j s t l r subs

let unify ?(max_depth=100) eqs f s t =
  apply_er f (mk_pb max_depth eqs s t)

