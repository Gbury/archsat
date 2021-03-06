(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Undo stack module *)
(* ************************************************************************ *)

module Stack = struct

  type op =
    (* Stack structure *)
    | Nil : op
    | Level : op * int -> op
    (* Undo operations *)
    | Set : 'a ref * 'a * op -> op
    | Call1 : ('a -> unit) * 'a * op -> op
    | Call2 : ('a -> 'b -> unit) * 'a * 'b * op -> op
    | Call3 : ('a -> 'b -> 'c -> unit) * 'a * 'b * 'c * op -> op
    | CallUnit : (unit -> unit) * op -> op

  type aref = Ref : 'a ref -> aref

  type t = {
    section : Section.t;
    mutable stack : op;
    mutable last  : int;
    mutable refs  : aref list;
  }

  type level = int

  let dummy_level = -1

  let create section = {
    section;
    stack = Nil;
    last = dummy_level;
    refs = [];
  }

  let attach t r = t.refs <- (Ref r) :: t.refs

  let register_set t ref value = t.stack <- Set(ref, value, t.stack)
  let register_ref t ref = register_set t ref !ref

  let register_undo t f = t.stack <- CallUnit (f, t.stack)
  let register1 t f x = t.stack <- Call1 (f, x, t.stack)
  let register2 t f x y = t.stack <- Call2 (f, x, y, t.stack)
  let register3 t f x y z = t.stack <- Call3 (f, x, y, z, t.stack)

  let curr = ref 0

  let push t =
    (* First insert Set callbacks for attached refs *)
    List.iter (function Ref r -> register_ref t r) t.refs;
    (* Then push a new level on the stack *)
    let level = !curr in
    Util.debug ~section:t.section "Push (#%d)" level;
    t.stack <- Level (t.stack, level);
    t.last <- level;
    incr curr

  let rec level t =
    match t.stack with
    | Level (_, lvl) -> lvl
    | _ -> push t; level t

  let backtrack t lvl =
    let rec pop = function
      | Nil -> assert false
      | Level (op, level) as current ->
        if level = lvl then begin
          t.stack <- current;
          t.last <- level
        end else
          pop op
      | Set (ref, x, op) -> ref := x; pop op
      | CallUnit (f, op) -> f (); pop op
      | Call1 (f, x, op) -> f x; pop op
      | Call2 (f, x, y, op) -> f x y; pop op
      | Call3 (f, x, y, z, op) -> f x y z; pop op
    in
    Util.enter_prof t.section;
    Util.debug ~section:t.section "Backtracking to point #%d" lvl;
    pop t.stack;
    Util.exit_prof t.section

  let pop t = backtrack t (t.last)

end

(* Hashtbl module *)
(* ************************************************************************ *)

module Hashtbl(K : Hashtbl.HashedType) = struct

  module H = Hashtbl.Make(K)

  type key = K.t
  type 'a t = {
    tbl : 'a H.t;
    stack : Stack.t;
  }

  let create ?(size=256) stack = {tbl = H.create size; stack; }

  let mem {tbl; _} x = H.mem tbl x
  let find {tbl; _} k = H.find tbl k

  let add t k v =
    Stack.register2 t.stack H.remove t.tbl k;
    H.add t.tbl k v

  let remove t k =
    try
      let v = find t k in
      Stack.register3 t.stack H.add t.tbl k v;
      H.remove t.tbl k
    with Not_found -> ()

  let fold t f acc = H.fold f t.tbl acc

  let iter f t = H.iter f t.tbl

  let snapshot t = H.copy t.tbl

end

