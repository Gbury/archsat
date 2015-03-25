
(* E-Unification module *)

(* Implementation follows from :
 * http://gbury.eu/public/rigid.pdf
*)

let log_section = Util.Section.make "rigid"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)
module H = Hashtbl.Make(Expr.Term)
module G = Graph.Persistent.Digraph.Concrete(Expr.Term)
module T = Graph.Traverse.Dfs(G)

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

type rule =
  | ER
  | RRBS
  | LRBS

type problem = {
  eqs : (term * term) Parray.t;
  last_rule : rule;
  goal : term * term;
  lrbs_index : int;
  constr : solved_form list;
}

(* Printing *)
(* ************************************************************************ *)

let rec debug_ss b = function
  | Empty -> Printf.bprintf b "."
  | Equal(t, Empty) | Greater (t, Empty) ->
    Printf.bprintf b "%a" Expr.debug_term t
  | Equal (t, s) -> Printf.bprintf b "%a = %a" Expr.debug_term t debug_ss s
  | Greater (t, s) -> Printf.bprintf b "%a > %a" Expr.debug_term t debug_ss s

(* Exceptions *)
(* ************************************************************************ *)

exception Sat_solved_form of simple_system (** NOT exported *)
exception Unsat_solved_form (** NOT exported *)

exception Not_unifiable

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
  if Expr.Term.equal t t' then Comparison.Eq
  else match Lpo.compare t t' with
    | Comparison.Incomparable -> ss_compare_aux t t' s
    | cmp -> cmp

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
    if Expr.Var.compare f g < 0 then
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
    if not (Expr.Var.equal f g) then false
    else List.for_all2 (ss_equal s) f_args g_args
  | _ -> true

let rec check_equal t = function
  | Empty -> true
  | Greater (t', s) -> check_equal_aux s t t' && check_greater t s
  | Equal (t', s) -> check_equal_aux s t t' && check_equal t s

let valid_ss = function
  | Empty -> true
  | Greater (t, s) -> check_greater t s
  | Equal (t, ((Equal(t', _) | Greater (t', _)) as s)) ->
    Expr.Term.compare t t' > 0 && check_equal t s
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
  | { Expr.term = Expr.App (f, _, l) } as t -> t :: Util.list_flatmap subterms l
  | t -> [t]

let add_edge g t t' = incr_in { g with graph = G.add_edge g.graph t t' } t'

let add_vertex g v = G.fold_vertex
    (fun t g -> if Lpo.compare t v = Comparison.Lt then add_edge g t v else g)
    g.graph { g with graph = G.add_vertex g.graph v }

let graph s =
  let l = Util.list_flatmap (fun (t, t') -> subterms t @ subterms t') s.constraints in
  let l = List.sort_uniq Expr.Term.compare l in
  let l = List.sort (fun t t' -> Comparison.to_total (Lpo.compare t t')) l in
  let g = List.fold_left add_vertex empty_graph l in
  let g = List.fold_left (fun g (t, t') -> add_edge g t t') g s.constraints in
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

let valid_sf sf =
  try
    let levels = H.create 64 in
    find_ss (graph sf) levels 0 Empty;
    false
  with
  | Unsat_solved_form -> false
  | Sat_solved_form _ -> true

(* Computing solved forms *)
(* ************************************************************************ *)

let sf_empty = {
  solved = Unif.empty;
  constraints = [];
}

let sf_belongs sf (s, t) =
  List.exists (fun (s', t') ->
      Expr.Term.equal s s' && Expr.Term.equal t t') sf.constraints

let rec eval_ty subst = function
  | { Expr.ty = Expr.TyVar _ } -> assert false
  | { Expr.ty = Expr.TyMeta m } as ty ->
    begin try eval_ty subst (Unif.get_ty subst m) with Not_found -> ty end
  | { Expr.ty = Expr.TyApp (f, args) } ->
    Expr.type_app f (List.map (eval_ty subst) args)

let rec add_eq sf s t =
  let s = Unif.follow_term sf.solved s in
  let t = Unif.follow_term sf.solved t in
  match s, t with
      | _ when Expr.Term.equal s t -> [sf]
      | { Expr.term = Expr.Var _ }, _
      | _, { Expr.term = Expr.Var _ } ->
        assert false
      | ({ Expr.term = Expr.Meta m } as v), w
      | w, ({ Expr.term = Expr.Meta m } as v) ->
        if Unif.occurs_check_term sf.solved v w then []
        else add_subst sf m w
      | { Expr.term = Expr.App (f, f_ty_args, f_args) },
        { Expr.term = Expr.App(g, g_ty_args, g_args) } ->
        if Expr.Var.compare f g = 0 then begin
          try
            let u = List.fold_left2 Unif.robinson_ty
                sf.solved f_ty_args g_ty_args in
            List.fold_left2 add_eq_set [{sf with solved = u}] f_args g_args
          with Unif.Not_unifiable_ty _ ->
            []
        end else
          []

and add_eq_set l s t = Util.list_flatmap (fun sf -> add_eq sf s t) l

and add_subst sf m t =
  if Expr.(Ty.equal m.meta_var.var_type (eval_ty sf.solved t.t_type)) then begin
    log 15 "Subst : %a -> %a" Expr.debug_meta m Expr.debug_term t;
    List.fold_left (fun acc (s, t) -> add_gt_set acc t s)
      [{solved = Unif.bind_term sf.solved m t; constraints = []}] sf.constraints
  end else begin
    log 15 "Refused subst : %a -> %a" Expr.debug_meta m Expr.debug_term t;
    []
  end

and add_gt sf s t =
  let s = Unif.follow_term sf.solved s in
  let t = Unif.follow_term sf.solved t in
  match s, t with
      | { Expr.term = Expr.Var _ }, _
      | _, { Expr.term = Expr.Var _ } ->
        assert false
      | { Expr.term = Expr.Meta _ }, _
        when Unif.occurs_check_term sf.solved s t -> []
      | _, { Expr.term = Expr.Meta _ }
        when Unif.occurs_check_term sf.solved t s -> [sf]
      | { Expr.term = Expr.Meta _ }, _ | _, { Expr.term = Expr.Meta _ }
        when sf_belongs sf (s, t) -> []
      | { Expr.term = Expr.Meta _ }, _ | _, { Expr.term = Expr.Meta _ } ->
        [{sf with constraints = (t, s) :: sf.constraints }]
      | { Expr.term = Expr.App (f, _, f_args) },
        { Expr.term = Expr.App (g, _, g_args) } ->
        begin match Expr.Var.compare f g with
          | n when n > 0 ->
            List.fold_left (fun acc ti -> add_gt_set acc s ti) [sf] g_args
          | n when n < 0 ->
            Util.list_flatmap (fun si -> add_eq sf si t @ add_gt sf si t) f_args
          | _ (* f = g *) ->
            let res = Util.list_flatmap (fun si -> add_eq sf si t @ add_gt sf si t) f_args in
            let eq = [sf] in
            fst (List.fold_left2 (fun (res, eq) si ti ->
                let h = add_gt_set eq si ti in
                let h = List.fold_left (fun h' tj -> add_gt_set h' s tj) h g_args in
                res @ h, add_eq_set eq si ti
              ) (res, eq) f_args g_args)
        end

and add_gt_set l s t = Util.list_flatmap (fun sf -> add_gt sf s t) l

let rec sf_set_sat = function
    | [] -> []
    | (sf :: r) as l ->
      if valid_sf sf then
        l
      else
        sf_set_sat r

(* BSE Calculus *)
(* ************************************************************************ *)

let mk_pb l u v =
  let a = Parray.of_list l in
  {
    eqs = a;
    goal = (u, v);
    last_rule = ER;
    lrbs_index = -1;
    constr = [sf_empty];
  }

let rec apply_er acc k pb =
  let (s, t) = pb.goal in
  match sf_set_sat (add_eq_set pb.constr s t) with
  | [] -> apply_rrbs acc k pb
  | l -> k (List.rev_append l acc)

and apply_rrbs acc k pb =
  let (a, b) = pb.goal in
  rrbs_aux acc (fun res ->
      rrbs_aux res (fun res ->
          apply_lrbs res k pb
        ) pb b a
    ) pb a b

and rrbs_aux acc k pb s t =
  match sf_set_sat (add_gt_set pb.constr s t) with
  | [] -> k acc
  | sat ->
    let pb = { pb with constr = sat } in
    begin match pb.last_rule with
      | LRBS -> rrbs_index acc k pb s t (Parray.make 1 (Parray.get pb.eqs pb.lrbs_index)) 0 
      | _ -> rrbs_index acc k pb s t pb.eqs 0
    end

and rrbs_index acc k pb s t eqs i =
  if i >= Parray.length eqs then
    apply_lrbs acc k pb
  else begin
    let (l, r) = Parray.get eqs i in
    let subs = subterms s in
    rrbs_eq_pre acc (fun res ->
        rrbs_eq_pre res (fun res ->
            rrbs_index res k pb s t eqs (i + 1)
          ) pb s t r l subs
      ) pb s t l r subs
  end

and rrbs_eq_pre acc k pb s t l r subs =
  match sf_set_sat (add_gt_set pb.constr l r) with
  | [] -> k acc
  | sat -> rrbs_eq acc k { pb with constr = sat } s t l r subs

and rrbs_eq acc k pb s t l r = function
  | [] -> k acc
  | { Expr.term = Expr.Meta _ } :: subs -> rrbs_eq acc k pb s t l r subs
  | p :: subs ->
    begin match sf_set_sat (add_eq_set pb.constr l p) with
      | [] -> rrbs_eq acc k pb s t l r subs
      | sat ->
        let s' = Expr.term_replace (p,r) s in
        apply_er acc (fun res -> rrbs_eq res k pb s t l r subs)
          { pb with last_rule = RRBS; constr = sat; goal = (s', t) }
    end

and apply_lrbs acc k pb = k acc

let unify eqs s t =
  match apply_er [] (fun x -> x) (mk_pb eqs s t) with
  | [] -> raise Not_unifiable
  | l -> List.map (fun sf -> sf.solved) l
