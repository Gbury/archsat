(*
   Persistent index for terms.
   Currently only discrimantes according to the head symbol.
*)
(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(struct type t = int let compare = compare end)
module S = CCMultiSet.Make(Expr.Term)

type t = S.t M.t

let empty = M.empty

let var_id v = (Expr.(v.var_id) : Expr.var_id :> int)

let head = function
  | { Expr.term = Expr.App(f,_, _) } -> Some f
  | _ -> None

let find e t =
  match head e with
  | None -> S.empty
  | Some v -> try M.find (var_id v) t with Not_found -> S.empty

let get e t =
  S.fold (find e t) [] (fun acc _ u -> u :: acc)

let add e t =
  match head e with
  | Some v ->
    let s = find e t in
    M.add (var_id v) (S.add s e) t
  | None -> t

let remove e t =
  match head e with
  | Some v ->
    let s = find e t in
    M.add (var_id v) (S.remove s e) t
  | None -> t
