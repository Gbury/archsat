(*
   Persistent index for terms.
   Currently only discrimnates according to the head symbol.
*)

(* Fingerprint index *)
(* ************************************************************************ *)

module Mt = Map.Make(Expr.Term)

module Fingerprint = struct
  type t = Expr.ty Position.res

  let discr = function
    | Position.Var -> 0
    | Position.Top _ -> 1
    | Position.Possible -> 2
    | Position.Impossible -> 3

  let compare f f' =
    let open Position in
    match f, f' with
    | Var, Var | Possible, Possible | Impossible, Impossible -> 0
    | Top s, Top s' -> Expr.Id.compare s s'
    | _ -> discr f - discr f'
  end

module Mf = Map.Make(Fingerprint)

module Make(T: Set.OrderedType) = struct

  module S = Set.Make(T)

  type node =
    | Empty
    | Leaf of S.t Mt.t
    | Node of node Mf.t

  type t = {
    key : Position.t list;
    trie : node;
  }

  let rec of_list = function
    | [] -> Position.root
    | i :: r -> Position.arg (i - 1) (of_list r)

  let master_key = List.map of_list [[]; [1]; [2]; [3]; [1; 1]; [1; 2]]

  let empty = {
    key = master_key;
    trie = Empty;
  }

  let fp_aux e p = fst @@ Position.Term.apply p e
  let fp l e = List.map (fp_aux e) l

  let findt e m = try Mt.find e m with Not_found -> S.empty
  let findf f m = try Mf.find f m with Not_found -> Empty

  let rec modify action e c f t =
    match f, t with
    | [], Leaf m ->
      let s = findt e m in
      Leaf (Mt.add e (action c s) m)
    | [], Empty ->
      Leaf (Mt.singleton e (action c S.empty))
    | f' :: r, Node m ->
      let t' = findf f' m in
      Node (Mf.add f' (modify action e c r t') m)
    | f' :: r, Empty ->
      Node (Mf.singleton f' (modify action e c r Empty))
    | _ -> assert false

  let add e c t = { t with trie = modify S.add e c (fp t.key e) t.trie }

  let remove e c t = { t with trie = modify S.remove e c (fp t.key e) t.trie }

  let rec find compat acc l t =
    match l, t with
    | _, Empty -> acc
    | [], Leaf m -> Mt.fold (fun e s acc ->
        if S.is_empty s then acc else (e, s) :: acc) m acc
    | f :: r , Node m ->
      Mf.fold (fun f' t' acc' -> if compat f f' then find compat acc' r t' else acc') m acc
    | _ -> assert false

  let compat_unif f f' = true &&
    let open Position in
    match f, f' with
    | Top f1, Top f2 -> Expr.Id.equal f1 f2
    | Impossible, (Top _ | Var) | (Top _ | Var), Impossible -> false
    | _ -> true

  let compat_match f f' = true &&
    (* can f' be 'sustituted' to be equal to f ? *)
    let open Position in
    match f with
    | Top f1 -> begin match f' with
        | Top f2 -> Expr.Id.equal f1 f2
        | Var | Possible -> true
        | Impossible -> false
      end
    | Var -> f' = Var || f' = Possible
    | Possible -> f' = Possible
    | Impossible -> f' = Possible || f' = Impossible

  let find_unify e t =
    CCList.filter_map (fun (e', s) ->
        match Unif.Robinson.find e e' with
        | Some u -> Some (e', u, S.elements s) | None -> None
      ) (find compat_unif [] (fp t.key e) t.trie)

  let find_match e t =
    let l = find compat_match [] (fp t.key e) t.trie in
    CCList.filter_map (fun (e', s) ->
        match Unif.Match.find e e' with
        | Some m -> Some (e', m, S.elements s) | None -> None
      ) l

end

(* Simple index *)
(* ************************************************************************ *)

(*
module Mi = Map.Make(struct type t = int let compare = compare end)

module Make(T: Set.OrderedType) = struct

  module S = Set.Make(T)

  type t = {
    map : S.t Mt.t Mi.t;
    univ : S.t Mt.t;
  }

  let empty = {
    map = Mi.empty;
    univ = Mt.empty;
  }

  let findi i m = try Mi.find i m with Not_found -> Mt.empty
  let findt e m = try Mt.find e m with Not_found -> S.empty

  let add e c t =
    match e with
    | { Expr.term = Expr.App(f,_,_) } ->
      let m = findi (var_id f) t.map in
      let s = findt e m in
      { t with map = Mi.add (var_id f) (Mt.add e (S.add c s) m) t.map }
    | { Expr.term = Expr.Meta { Expr.meta_id = v; _ } } ->
      let s = findt e t.univ in
      { t with univ = Mt.add e (S.add c s) t.univ }
    | { Expr.term = Expr.Var _ } -> assert false

  let remove e c t =
    match e with
    | { Expr.term = Expr.App(f,_,_) } ->
      let m = findi (var_id f) t.map in
      let s = findt e m in
      { t with map = Mi.add (var_id f) (Mt.add e (S.remove c s) m) t.map }
    | { Expr.term = Expr.Meta { Expr.meta_id = v; _ } } ->
      let s = findt e t.univ in
      { t with univ = Mt.add e (S.remove c s) t.univ }
    | { Expr.term = Expr.Var _ } -> assert false

  let unify_aux e map acc =
    Mt.fold (fun e' s acc' ->
        match Unif.Robinson.find_unifier e e' with
        | None -> acc'
        | Some u -> (e', u, S.elements s) :: acc'
      ) map acc

  let unify e t =
    match e with
    | { Expr.term = Expr.App(f,_,_) } ->
      let m = findi (var_id f) t.map in
      unify_aux e m (unify_aux e t.univ [])
    | { Expr.term = Expr.Meta { Expr.meta_id = v; _ } } ->
      Mi.fold (fun _ m acc -> unify_aux e m acc) t.map (unify_aux e t.univ [])
    | { Expr.term = Expr.Var _ } -> assert false

end
*)

