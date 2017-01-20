(*
   Persistent index for terms.
   Currently only discrimnates according to the head symbol.
*)

module Mt = Map.Make(Expr.Term)

(* Statistics *)
(* ************************************************************************ *)

let s_tries = Util.Stats.mk "tries"
let s_found = Util.Stats.mk "found"
let s_success = Util.Stats.mk "success"

let s_group = Util.Stats.bundle [s_success; s_found; s_tries]

(* Common signature *)
(* ************************************************************************ *)

module type S = sig

  type t
  type value

  val add : Expr.term -> value -> t -> t
  val remove : Expr.term -> value -> t -> t
  val find_unify : Expr.term -> t -> (Expr.term * Unif.t * value list) list
  val find_match : Expr.term -> t -> (Expr.term * Match.t * value list) list
end

(* Simple (and very naive) index *)
(* ************************************************************************ *)

(* This is designed as a reference implementation against which to compare. *)

module Simple(T: Set.OrderedType) = struct

  module S = Set.Make(T)

  type t = {
    section : Util.Section.t;
    map: S.t Mt.t;
  }

  let empty section = { section; map = Mt.empty; }

  let find t m =
    try Mt.find t m.map
    with Not_found -> S.empty

  let add t x m =
    let s = find t m in
    { m with map = Mt.add t (S.add x s) m.map }

  let remove t x m =
    let s = find t m in
    { m with map = Mt.add t (S.remove x s) m.map }

  let find_unify pat m =
    let aux t s acc =
      match Unif.Robinson.find ~section:m.section pat t with
      | None -> acc
      | Some u -> (t, u, S.elements s) :: acc
    in
    Mt.fold aux m.map []

  let find_match pat m =
    let aux t s acc =
      match Match.find ~section:m.section pat t with
      | None -> acc
      | Some u -> (t, u, S.elements s) :: acc
    in
    Mt.fold aux m.map []

end

(* Fingerprint index *)
(* ************************************************************************ *)

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

  let print = Position.print_res Expr.Print.const_ty

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
    section : Util.Section.t;
    unif_section : Util.Section.t;
  }

  let rec of_list = function
    | [] -> Position.root
    | i :: r -> Position.arg (i - 1) (of_list r)

  let master_key = [[]; [0]; [1]; [2]; [0; 0]; [0; 1]]

  let empty ?(key=master_key) section =
    Util.Stats.attach section s_group;
    {
      section;
      trie = Empty;
      key = List.map of_list key;
      unif_section = Util.Section.make ~parent:section "unif";
    }

  let fp_aux e p = fst @@ Position.Term.apply p e
  let fp l e = List.map (fp_aux e) l

  let fingerprint t e = fp t.key e

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

  let add e c t =
    Util.enter_prof t.section;
    let res = { t with trie = modify S.add e c (fp t.key e) t.trie } in
    Util.exit_prof t.section;
    res

  let remove e c t =
    Util.enter_prof t.section;
    let res = { t with trie = modify S.remove e c (fp t.key e) t.trie } in
    Util.exit_prof t.section;
    res

  let rec find compat acc l t =
    match l, t with
    | _, Empty -> acc
    | [], Leaf m -> Mt.fold (fun e s acc ->
        if S.is_empty s then acc else (e, s) :: acc) m acc
    | f :: r , Node m ->
      Mf.fold (fun f' t' acc' -> if compat f f' then find compat acc' r t' else acc') m acc
    | _ -> assert false

  let compat_unif f f' = (* Can f and f' be unified ? *)
    let open Position in
    match f, f' with
    | Top f1, Top f2 -> Expr.Id.equal f1 f2
    | Impossible, (Top _ | Var)
    | (Top _ | Var), Impossible -> false
    | _ -> true

  let compat_match f f' = (* can f be 'sustituted' to be equal to f' ? *)
    let open Position in
    match f, f' with
    (* To match an application, you need an application with the same function. *)
    | Top f1, Top f2 -> Expr.Id.equal f1 f2
    | Top _, (Var | Possible | Impossible) -> false
    (* A var can match a var (iff it's the same var), and an application.
       However, since we are matching, a var cannot match a 'possible'. *)
    | Var, (Top _ | Var) -> true
    | Var, (Possible | Impossible) -> false
    (* A possible can match an application, an impossible, and another possible
       (iff both possible derive from the same var at the same place. ) *)
    | Possible, (Var | Impossible | Possible | Top _) -> true
    (* An impossible can only match an impossible. *)
    | Impossible, Impossible -> true
    | Impossible, (Top _ | Var | Possible) -> false

  let find_unify e t =
    Util.enter_prof t.section;
    Util.Stats.incr s_tries t.section;
    let l = find compat_unif [] (fp t.key e) t.trie in
    Util.Stats.incr ~k:(List.length l) s_found t.section;
    let res = CCList.filter_map (fun (e', s) ->
        match Unif.Robinson.find ~section:t.unif_section e e' with
        | Some u -> Some (e', u, S.elements s) | None -> None
      ) l in
    Util.Stats.incr ~k:(List.length res) s_success t.section;
    Util.exit_prof t.section;
    res

  let find_match pat t =
    Util.enter_prof t.section;
    Util.Stats.incr s_tries t.section;
    let l = find compat_match [] (fp t.key pat) t.trie in
    Util.Stats.incr ~k:(List.length l) s_found t.section;
    let res =
      CCList.filter_map (fun (e, s) ->
          match Match.find ~section:t.unif_section pat e with
          | Some m -> Some (e, m, S.elements s) | None -> None
        ) l in
    Util.Stats.incr ~k:(List.length res) s_success t.section;
    Util.exit_prof t.section;
    res

end

