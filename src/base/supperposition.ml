(*
   This module uses unitary supperposition to
   unify terms modulo equality.
   For a reference, see :
   'E, a brainiac theorem prover' by shulz.
*)
(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)

module MS = CCMultiSet.Make(struct
    type t = Expr.Ty.t Expr.Meta.t let compare = Expr.Meta.compare end)

(* Represents equality of disequality beetween terms *)
type atom =
  | Eq of Expr.Term.t * Expr.Term.t
  | Neq of Expr.Term.t * Expr.Term.t

let compare_atoms e e' = match e, e' with
  | Eq _, Neq _ -> -1
  | Neq _, Eq _ -> 1
  | Eq (a, b), Eq (a', b') | Neq(a, b), Neq(a', b') ->
    match Expr.Term.compare a a' with
    | 0 -> Expr.Term.compare b b'
    | x -> x

(* Type for unit clauses, i.e clauses with at most one equation.
   Whenever we obtain a clause with
   no equation, it means we have found a list of instanciations to do.
   The multi set represents a constraint: the count of any elements
   should not exceed a fixed amount. *)
type clause = {
  lit : atom option;
  acc : Unif.t list;
  constr : MS.t;
  parents : clause list;
}

let compare_cl c c' =
  match c.lit, c'.lit with
  | None, Some _ -> -1
  | Some _, None -> 1
  | None, None -> Util.lexicograph Unif.compare c.acc c'.acc
  | Some a, Some a' ->
    match compare_atoms a a' with
    | 0 -> Util.lexicograph Unif.compare c.acc c'.acc
    | x -> x

let c_leq c c' =
  match c.lit with
  | None -> true
  | Some _ -> false

module Q = CCHeap.Make(struct type t = clause let leq = c_leq end)
module S = Set.Make(struct type t = clause let compare = compare_cl end)

type t = {
  clauses : S.t;
  t_index : Index.t;
  cl_index : (clause list * clause list) M.t;
}

(* Constructors *)
(* ************************************************************************ *)

let mk_cl e = {
  lit = Some e;
  acc = [];
  constr = MS.empty;
  parents = [];
}

let mk_eq a b = mk_cl (Eq (a, b))
let mk_neq a b = mk_cl (Neq (a, b))

let empty = {
  clauses = S.empty;
  t_index = Index.empty;
  cl_index = M.empty;
}

let add_left t c m =
  let l, l' = try M.find t m with Not_found -> [], [] in
  M.add t (c :: l, l') m

let add_right t c m =
  let l, l' = try M.find t m with Not_found -> [], [] in
  M.add t (l, c :: l') m

let remove_left t c m =
  let l, l' = try M.find t m with Not_found -> [], [] in
  M.add t (List.filter (fun c' -> compare_cl c c' <> 0) l, l') m

let remove_right t c m =
  let l, l' = try M.find t m with Not_found -> [], [] in
  M.add t (l, List.filter (fun c' -> compare_cl c c' <> 0) l') m

let mem_clause c t = S.mem c t.clauses

let add_clause c t =
  assert (not (mem_clause c t));
  let a, b = match c.lit with
    | Some Eq (a, b) | Some Neq (a, b) -> a,b
    | None -> assert false
  in {
    clauses = S.add c t.clauses;
    t_index = Index.add a (Index.add b t.t_index);
    cl_index = add_left a c (add_right b c t.cl_index);
  }

let rm_clause c t =
  assert (mem_clause c t);
  let a, b = match c.lit with
    | Some Eq (a, b) | Some Neq (a, b) -> a,b
    | None -> assert false
  in {
    clauses = S.remove c t.clauses;
    t_index = Index.remove a (Index.remove b t.t_index);
    cl_index = remove_left a c (remove_right b c t.cl_index);
  }

(* Inference rules *)
(* ************************************************************************ *)

let equality_resolution c =
  match c.lit with
  | Some Neq (a, b) ->
    begin match Unif.find_unifier a b with
      | Some u -> [{ lit = None; acc = u :: c.acc; constr = c.constr; parents = [c] }]
      | None -> []
    end
  | _ -> []

let sup_neg c c' = assert false

(* Main functions *)
(* ************************************************************************ *)

let simplify_clause c p = None

let simplify c p =
  match simplify_clause c p with
  | Some c' -> c'
  | None -> c

let cheap_simplify c p = c

let redundant c p = false

let generate c p =
  equality_resolution c

let trivial c p =
  match c.lit with
  | Some Eq (a, b) when Expr.Term.equal a b -> true
  | _ -> false

let is_descendant p c = List.memq p c.parents

(* Main loop *)
(* ************************************************************************ *)

type res =
  | Model of t
  | Found of Unif.t list

let rec discount_loop p_set u =
  match Q.take u with
  | None -> Model p_set
  | Some (u, c) ->
    let c = simplify c p_set in
    if redundant c p_set then
      discount_loop p_set u
    else begin
      if c.lit = None then
        Found (c.acc)
      else begin
        let p_set = add_clause c p_set in
        let p_set, t, u = S.fold (fun p (p_set, t, u) ->
            let p_aux = rm_clause p p_set in
            match simplify_clause p p_aux with
            | None -> (p_set, t, u)
            | Some p' -> (p_aux, p :: t,
                          Q.filter (is_descendant p) u)
          ) p_set.clauses (p_set, [], u) in
        let t = List.rev_append t (generate c p_set) in
        let u = List.fold_left (fun acc p ->
            let p = cheap_simplify p p_set in
            if trivial p p_set then
              acc
            else
              Q.insert p acc
          ) u t in
        discount_loop p_set u
      end
    end

let add_eqs t l =
  discount_loop t (List.fold_left (fun q (a,b) ->
      Q.insert (mk_eq a b) q) Q.empty l)

let add_neq t p q =
  discount_loop t (Q.insert (mk_neq p q) Q.empty)

(* Wrappers/Helpers for unification *)
(* ************************************************************************ *)

let mk_unifier l f =
  let t = match add_eqs empty l with
    | Model t -> t
    | Found _ -> assert false
  in
  (fun p q -> match add_neq t p q with
     | Model _ -> ()
     | Found l -> List.iter f l)

