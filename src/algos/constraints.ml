
(* Constraint accumulators *)
(* ************************************************************************ *)

type 'a gen = unit -> 'a option

type ('a, 'b) fold = 'a gen -> 'b -> 'a gen

type ('a, 'b) t = {
  fold : ('a, 'b) fold;
  stream : 'a Gen.Restart.t;
}

let make g fold =
  let stream = Gen.persistent_lazy ~caching:false g in
  match stream () () with
  | None -> None
  | Some _ -> Some { stream; fold }

let add_constraint t l =
  let g = t.fold (t.stream ()) l in
  make g t.fold

(* Getters *)
(* ************************************************************************ *)

let gen t = t.stream ()

(* Helpers *)
(* ************************************************************************ *)

let from_merger gen merger start =
  let fold g b = Gen.merge (Gen.map merger (Gen.product g (gen b))) in
  match make start fold with
  | None -> raise (Invalid_argument "Constraints.from_merger: start gern should be non-empty")
  | Some t -> t

