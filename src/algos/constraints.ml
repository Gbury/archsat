
(* Constraint accumulators *)
(* ************************************************************************ *)

type 'a gen = unit -> 'a option

type 'a fold = 'a gen ->  Expr.formula list -> 'a gen

type t =
  | Stream : 'a Gen.Restart.t * 'a fold -> t

let make g fold =
  let e = Gen.persistent_lazy ~caching:false g in
  match e () () with
  | Some _ -> Some (Stream (e, fold))
  | None -> None

let add_constraint t l =
  match t with Stream (s, f) ->
    let g = f (s ()) l in
    make g f

(* Helpers *)
(* ************************************************************************ *)

let from_merger gen m =
  let f g l = Gen.merge (Gen.map m (Gen.product g (gen l))) in
  match make (gen []) f with
  | None -> raise (Invalid_argument "Constraints.from_merger")
  | Some t -> t

