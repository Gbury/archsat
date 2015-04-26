(*
   This module uses unitary supperposition to
   unify terms modulo equality.
   For a reference, see :
   'E, a brainiac theorem prover' by shulz.
*)

(* Clauses *)
(* ************************************************************************ *)

module MS = CCMultiSet.Make(struct
    type t = Expr.Ty.t Expr.Meta.t let compare = Expr.Meta.compare end)

(* Type for unit clauses, i.e clauses with at most one equation *)
type clause = {
  eq : bool; (* Is the clause/atom positive (it is an equality), or negative (a difference) ? *)
  lit : (Expr.Term.t * Expr.Term.t) option;
  acc : Unif.t list;
  constr : MS.t;
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

(* TODO: better heuristic for clause selection. *)
let c_leq c c' =
  match c.lit with
  | None -> true
  | Some _ -> false

(* Clauses *)
let mk_cl p a b = {
  eq = p;
  lit = Some (a, b);
  acc = [];
  constr = MS.empty;
  parents = [];
}

let ord a b = if Expr.Term.compare a b <= 0 then a, b else b, a

let mk_eq a b =
  let c, d = ord a b in
  mk_cl true c d

let mk_neq a b =
  let c, d = ord a b in
  mk_cl false c d

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

module I = Index.Make(struct type t = pos_cl let compare = compare_pos_cl end)

(* Supperposition state *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)
module Q = CCHeap.Make(struct type t = clause let leq = c_leq end)
module S = Set.Make(struct type t = clause let compare = compare_cl end)

type t = {
  clauses : S.t;
  active_index : I.t;
  inactive_index : I.t;
  continuation : Unif.t -> unit;
}

let empty f = {
  clauses = S.empty;
  active_index = I.empty;
  inactive_index = I.empty;
  continuation = f;
}

let mem_clause c t = S.mem c t.clauses

let fold_subterms f e side clause i =
  Position.Term.fold (fun i pos t -> f t { pos; side; clause } i) i e

let change_state f_set f_index c t =
  let a, b = match c.lit with
    | Some (a, b) -> a, b
    | None -> assert false
  in
  let l = match Lpo.compare a b with
    | Comparison.Lt -> [b, Right] | Comparison.Gt -> [a, Left]
    | Comparison.Incomparable -> [a, Left; b, Right]
    | Comparison.Eq -> assert false
  in
  let active_index =
    if c.eq then
      List.fold_left (fun i (t, side) ->
          f_index t { pos = Position.Term.root; side; clause = c } i)
        t.active_index l
    else
      t.active_index
  in
  let inactive_index = List.fold_left (fun i (t, side) ->
      fold_subterms f_index t side c i) t.inactive_index l
  in
  {
    clauses = f_set c t.clauses;
    active_index;
    inactive_index;
    continuation = t.continuation;
  }

let add_clause = change_state S.add I.add
let rm_clause = change_state S.remove I.remove

(* Inference rules *)
(* ************************************************************************ *)

(* Equality resolution, alias ER *)
let equality_resolution c =
  if not c.eq then
    match c.lit with
    | Some (a, b) ->
      begin match Unif.find_unifier a b with
        | Some u -> [{ eq = true; lit = None; acc = u :: c.acc; constr = c.constr; parents = [c] }]
        | None -> []
      end
    | _ -> []
  else []

(* Supperposition rules, alias SN & SP *)
let do_supp active inactive =
  assert (active.pos = Position.Term.root);
  []

let add_neg_supp p_set c side acc pos p =
  let l = I.unify p p_set.active_index in
  CCList.flat_map (fun (s, u, l) ->
      CCList.flat_map (fun active ->
          do_supp active { clause = c; side; pos }
        ) l
    ) l @ acc

let supp_lit c p_set =
  let a, b = match c.lit with Some(a, b) -> a, b | None -> assert false in
  if c.eq then
    []
  else begin
    match Lpo.compare a b with
    | Comparison.Gt -> Position.Term.fold (add_neg_supp p_set c Left) [] a
    | Comparison.Lt -> Position.Term.fold (add_neg_supp p_set c Right) [] b
    | Comparison.Incomparable ->
      Position.Term.fold (add_neg_supp p_set c Left)
        (Position.Term.fold (add_neg_supp p_set c Right) [] b) a
    | Comparison.Eq -> assert false
  end

(* Main functions *)
(* ************************************************************************ *)

(* Applies: RN, RP, PS, NS, ES *)
let simplify_clause c p = None

let simplify c p =
  match simplify_clause c p with
  | Some c' -> c'
  | None -> c

(* Applies: RN, RP *)
let cheap_simplify c p = c

(* Applies: ES *)
let redundant c p = false

(* Applies: ER (OK), SP, SN *)
let generate c p =
  List.rev_append (equality_resolution c) (supp_lit c p)

(* Applies: TD1 (OK) *)
let trivial c p =
  match c.eq, c.lit with
  | true, Some (a, b) when Expr.Term.equal a b -> true
  | _ -> false

let is_descendant p c = List.memq p c.parents

(* Main loop *)
(* ************************************************************************ *)

let rec discount_loop p_set u =
  match Q.take u with
  | None -> p_set
  | Some (u, c) ->
    let c = simplify c p_set in
    if redundant c p_set then
      discount_loop p_set u
    else begin
      if c.lit = None then begin
        List.iter p_set.continuation c.acc;
        discount_loop p_set u
      end else begin
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
  let aux q (a,b) =
    let c = mk_eq a b in
    if trivial c t then
      Q.insert c q
    else q
  in
  discount_loop t (List.fold_left aux Q.empty l)

let add_neq t p q =
  discount_loop t (Q.insert (mk_neq p q) Q.empty)

(* Wrappers/Helpers for unification *)
(* ************************************************************************ *)

let mk_unifier l f =
  let t = add_eqs (empty f) l in
  (fun p q -> let _ = add_neq t p q in ())

