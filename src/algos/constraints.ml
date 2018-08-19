(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Some helpers *)
(* ************************************************************************ *)

let mapi f =
  let i = ref (-1) in
  let aux x = incr i; f !i x in
  Gen.map aux

(* Constraint accumulators *)
(* ************************************************************************ *)

type ('a, 'b, 'c) refiner = 'b -> 'a -> ('a * 'c) Gen.t

type ('a, 'c) elt = {
  elt : 'a;
  reason : (int * 'c) option;
}

type ('a, 'b, 'c) t = {
  depth : int;
  parent : (('a, 'b, 'c) t * 'b) option;
  refiner : ('a, 'b, 'c) refiner;
  stream : ('a, 'c) elt Gen.Restart.t;
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
  { depth; parent; stream; refiner }

let make g refiner =
  let gen = Gen.map (fun elt -> { elt; reason = None; }) g in
  mk 0 None gen refiner

let add_constraint t b =
  let f = t.refiner b in
  let aux i e =
    let g = f e.elt in
    Gen.map (fun (x, c) -> { elt = x; reason = Some (i, c); }) g
  in
  let g = Gen.merge @@ mapi aux (t.stream ()) in
  mk (t.depth + 1) (Some (t, b)) g t.refiner

(* Helpers *)
(* ************************************************************************ *)

let from_merger gen merger start =
  let refiner st =
    let g = Gen.persistent_lazy @@ gen st in
    (fun x -> Gen.Restart.lift (Gen.flat_map (merger x)) g)
  in
  make start refiner

(* Graph dumping *)
(* ************************************************************************ *)

let opt pp fmt = function
  | None -> Format.fprintf fmt "\\<no state\\>"
  | Some t -> pp fmt t

let dump_gen pp_a fmt i x = Format.fprintf fmt "|<f%d> %a" i pp_a x.elt

let dump_node n pp_a pp_b fmt t =
  let b = match t.parent with
    | None -> None
    | Some (_, b) ->
      Format.fprintf fmt "tt%dt%d -> tt%dt%d [style=\"invis\"];@\n" n (t.depth - 1) n t.depth;
      Some b
  in
  Format.fprintf fmt "tt%dt%d [shape=record, label=\"%a %a\"];@\n"
    n t.depth (opt pp_b) b (fun fmt g -> Gen.iteri (dump_gen pp_a fmt) g) (t.stream ())

let dump_edge pp_c n fmt depth i (x : _ elt) =
  match x.reason with
  | None -> ()
  | Some (parent, r) ->
    Format.fprintf fmt "tt%dt%dr%d [label=\"%a\"];@\n" n depth i pp_c r;
    Format.fprintf fmt "tt%dt%d:f%d -> tt%dt%dr%d -> tt%dt%d:f%d;@\n" n (depth - 1) parent n depth i n depth i

let dump_edges pp_c n fmt t =
  Gen.iteri (dump_edge pp_c n fmt t.depth) (t.stream ())

let dump_t n pp_a pp_b pp_c fmt t =
  Format.fprintf fmt "%a@\n%a"
    (dump_node n pp_a pp_b) t
    (dump_edges pp_c n) t

let dump_aux n pp_a pp_b pp_c fmt t =
  let rec aux acc t =
    match t.parent with
    | None ->
      dump_node n pp_a pp_b fmt t;
      List.iter (dump_t n pp_a pp_b pp_c fmt) acc
    | Some (t', _) -> aux (t :: acc) t'
  in
  aux [] t

let dump pp_a pp_b pp_c fmt t i =
  Format.fprintf fmt "subgraph tt%d {@\n%a@\n}@." i (dump_aux i pp_a pp_b pp_c) t

let dumps pp_a pp_b pp_c fmt l =
  Format.fprintf fmt "digraph G {@\n splines=line;ranksep=4;@\n";
    List.iteri (fun i t -> dump pp_a pp_b pp_c fmt t i) l;
    Format.fprintf fmt "}@."


