
(* Some helpers *)
(* ************************************************************************ *)

let mapi f =
  let i = ref (-1) in
  let aux x = incr i; f !i x in
  Gen.map aux

(* Constraint accumulators *)
(* ************************************************************************ *)

type ('a, 'b) refiner = 'b -> 'a -> 'a Gen.t

type 'a elt = {
  elt : 'a;
  index : int;
  parent : int;
}

type ('a, 'b) t = {
  depth : int;
  parent : ('a, 'b) t option;
  refiner : ('a, 'b) refiner;
  stream : 'a elt Gen.Restart.t;
}

(* Getters *)
(* ************************************************************************ *)

let gen t =
  let g = t.stream () in
  Gen.map (fun e -> e.elt) g

(* Construction *)
(* ************************************************************************ *)

let mk depth parent g refiner =
  let stream = Gen.persistent_lazy ~caching:false g in
  match Gen.(Restart.lift get stream) with
  | None -> None
  | Some _ -> Some { depth; parent; stream; refiner }

let make g refiner =
  let gen = mapi (fun index elt -> { index; elt; parent = -1; }) g in
  mk 0 None gen refiner

let add_constraint t b =
  let i = ref (-1) in
  let f = t.refiner b in
  let aux e =
    let g = f e.elt in
    Gen.map (fun x ->
        incr i; { elt = x; index = !i; parent = e.index; }) g
  in
  let g = Gen.merge @@ Gen.map aux (t.stream ()) in
  mk (t.depth + 1) (Some t) g t.refiner

(* Helpers *)
(* ************************************************************************ *)

let from_merger gen merger start =
  let refiner st =
    let g = gen st in
    (fun x -> Gen.flat_map (merger x) g)
  in
  match make start refiner with
  | None -> raise (Invalid_argument "Constraints.from_merger: start generator should be non-empty")
  | Some t -> t

