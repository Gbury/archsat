
type 'a gen = unit -> 'a option

(* Streams (i.e non-empty generators) *)
(* ************************************************************************ *)

type 'a stream = {
  head : 'a;
  tail : 'a gen;
}

let stream_of_gen g =
  match Gen.get g with
  | Some x -> Some { head = x; tail = g; }
  | None -> None

let gen_of_stream s = Gen.append (Gen.singleton s.head) s.tail

(* Constraint accumulators *)
(* ************************************************************************ *)

type 'a fold = 'a gen ->  Expr.formula list -> 'a gen

type t =
  | Stream : 'a stream * 'a fold -> t

let make s fold = Stream (s, fold)

let add_constraint t l =
  match t with Stream (s, f) ->
    let g = gen_of_stream s in
    let g' = f g l in
    match stream_of_gen g' with
    | None -> None
    | Some s' -> Some (Stream (s', f))

let from_merger gen m = fun g l ->
  let g' = gen l in
  Gen.filter_map m (Gen.product g g')

