
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
  parent : int;
}

type ('a, 'b) t = {
  depth : int;
  parent : (('a, 'b) t * 'b) option;
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
  let gen = Gen.map (fun elt -> { elt; parent = -1; }) g in
  mk 0 None gen refiner

let add_constraint t b =
  let f = t.refiner b in
  let aux i e =
    let g = f e.elt in
    Gen.map (fun x -> { elt = x; parent = i; }) g
  in
  let g = Gen.merge @@ mapi aux (t.stream ()) in
  mk (t.depth + 1) (Some (t, b)) g t.refiner

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

(* Graph dumping *)
(* ************************************************************************ *)

let opt pp fmt = function
  | None -> Format.fprintf fmt "\\<none\\>"
  | Some t -> pp fmt t

let dump_gen pp_a fmt i x = Format.fprintf fmt "|<f%d> %a" i pp_a x.elt

let dump_node n pp_a pp_b fmt t =
  let b = match t.parent with
    | None -> None
    | Some (_, b) -> Some b
  in
  Format.fprintf fmt "tt%dt%d [shape=record, label=\"%a %a\"];@\n"
    n t.depth (opt pp_b) b (fun fmt g -> Gen.iteri (dump_gen pp_a fmt) g) (t.stream ())

let dump_edge n fmt depth i (x : _ elt) =
  Format.fprintf fmt "tt%dt%d:f%d -> tt%dt%d:f%d;@\n" n (depth - 1) x.parent n depth i

let dump_edges n fmt t =
  Gen.iteri (dump_edge n fmt t.depth) (t.stream ())

let dump_t n pp_a pp_b fmt t =
  Format.fprintf fmt "%a@\n%a"
    (dump_node n pp_a pp_b) t
    (dump_edges n) t

let dump_aux n pp_a pp_b fmt t =
  let rec aux acc t =
    match t.parent with
    | None ->
      dump_node n pp_a pp_b fmt t;
      List.iter (dump_t n pp_a pp_b fmt) acc
    | Some (t', _) -> aux (t :: acc) t'
  in
  aux [] t

let dump pp_a pp_b fmt t i =
  Format.fprintf fmt "subgraph tt%d {@\n%a@\n}@." i (dump_aux i pp_a pp_b) t

let dumps pp_a pp_b fmt l =
  Format.fprintf fmt "digraph G {@\n splines=line;ranksep=4;@\n";
    List.iteri (fun i t -> dump pp_a pp_b fmt t i) l;
    Format.fprintf fmt "}@."


