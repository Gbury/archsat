(*
   Persistent index fro terms.
   Currently only discrimantes according to the head symbol.
*)
(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(struct type t =int let compare =compare end)

type t = Expr.term list M.t

let empty = M.empty

let var_id v = (Expr.(v.var_id) : Expr.var_id :> int)

let head = function
  | { Expr.term = Expr.App(f,_, _) } -> Some f
  | _ -> None

let add e t =
  match head e with
  | Some v -> M.add (var_id v) e t
  | None -> t

let find e t =
  match head e with
  | Some v -> M.find (var_id v) t
  | None -> []

