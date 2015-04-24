(*
   Persistent index for terms.
   Currently only discrimnates according to the head symbol.
*)

(* Helpers *)
(* ************************************************************************ *)

let var_id v = (Expr.(v.var_id) : Expr.var_id :> int)

let head = function
  | { Expr.term = Expr.App(f,_, _) } -> Some f
  | _ -> None

(* Simple index *)
(* ************************************************************************ *)

module Mt = Map.Make(Expr.Term)
module Mi = Map.Make(struct type t = int let compare = compare end)

module Make(T: Set.OrderedType) = struct

  module S = Set.Make(T)

  type t = S.t Mt.t Mi.t
  type elt = T.t

  let empty = Mi.empty

  let find e t =
    match head e with
    | None -> Mt.empty
    | Some v -> try Mi.find (var_id v) t with Not_found -> Mt.empty

  let get e m = try Mt.find e m with Not_found -> S.empty

  let add e c t =
    match head e with
    | Some v ->
      let m = find e t in
      let s = get e m in
      Mi.add (var_id v) (Mt.add e (S.add c s) m) t
    | None -> t

  let remove e c t =
    match head e with
    | Some v ->
      let m = find e t in
      let s = get e m in
      Mi.add (var_id v) (Mt.add e (S.remove c s) m) t
    | None -> t

  let unify e t =
    let m = find e t in
    Mt.fold (fun e' s acc ->
        match Unif.find_unifier e e' with
        | None -> acc
        | Some u -> (e', u, S.elements s) :: acc
      ) m []

end
