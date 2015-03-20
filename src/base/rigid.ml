
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

type solved_form = {
  solved : Unif.t;
  constraints : (term * term) list; (* t < t' *)
}

type simple_system =
  | Empty (* () *)
  | Equal of term * simple_system (* t = ... *)
  | Greater of term * simple_system (* t > ... *)

type graph = {
  graph : G.t;
  incoming : int M.t;
}

(* Printing *)
(* ************************************************************************ *)

let rec debug_ss b = function
  | Empty -> ()
  | Equal(t, Empty) | Greater (t, Empty) ->
    Printf.bprintf b "%a" Expr.debug_term t
  | Equal (t, s) -> Printf.bprintf b "%a = %a" Expr.debug_term t debug_ss s
  | Greater (t, s) -> Printf.bprintf b "%a > %a" Expr.debug_term t debug_ss s

(* Exceptions *)
(* ************************************************************************ *)

exception Sat_solved_form
exception Unsat_solved_form

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
  if length s = G.nb_vertex g.graph then raise Sat_solved_form
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
  | Sat_solved_form -> true

(* Computing solved forms *)
(* ************************************************************************ *)

(* BSE Calculus *)
(* ************************************************************************ *)

