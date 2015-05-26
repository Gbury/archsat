(*
   Persistent index for terms.
   Currently only discrimnates according to the head symbol.
*)

(* Helpers *)
(* ************************************************************************ *)

let var_id v = (Expr.(v.index) : Expr.index :> int)

(* Simple index *)
(* ************************************************************************ *)

module Mt = Map.Make(Expr.Term)
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
        match Unif.find_unifier e e' with
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
