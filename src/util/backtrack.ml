
module Stack = struct

  let log_section = Util.Section.make "stack"
  let log i fmt = Util.debug ~section:log_section i fmt

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

  type t = {
    mutable stack : op;
    mutable level : int;
  }

  type level = int

  let dummy_level = -1

  let create () = {stack=Nil; level=0}

  let register_set t ref value = t.stack <- Set(ref, value, t.stack)
  let register_undo t f = t.stack <- CallUnit (f, t.stack)
  let register1 t f x = t.stack <- Call1 (f, x, t.stack)
  let register2 t f x y = t.stack <- Call2 (f, x, y, t.stack)
  let register3 t f x y z = t.stack <- Call3 (f, x, y, z, t.stack)

  let push t =
    log 5 "Push (%d)" t.level;
    t.stack <- Level (t.stack, t.level);
    t.level <- t.level + 1

  let level t =
    let res = t.level in
    push t;
    res

  let backtrack t lvl =
    let rec pop = function
      | Nil -> assert false
      | Level (op, level) as current ->
        if level = lvl then
          (t.stack <- current; t.level <- lvl)
        else
          pop op
      | Set (ref, x, op) -> ref := x; pop op
      | CallUnit (f, op) -> f (); pop op
      | Call1 (f, x, op) -> f x; pop op
      | Call2 (f, x, y, op) -> f x y; pop op
      | Call3 (f, x, y, z, op) -> f x y z; pop op
    in
    log 5 "Backtracking to level %d" lvl;
    pop t.stack

  let pop t = backtrack t (t.level - 1)

end

module HashtblBack(K : Hashtbl.HashedType) = struct

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
    let v = find t k in
    Stack.register3 t.stack H.add t.tbl k v;
    H.remove t.tbl k

  let fold t f acc = H.fold f t.tbl acc

  let iter f t = H.iter f t.tbl
end

