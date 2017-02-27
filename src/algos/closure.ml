
(* Modules signature *)
(* ************************************************************************ *)

(** Closure keys*)
module type Key = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(** Union-find algorithm signature *)
module type S = sig
  type var
  type 'a t
  type 'a eq_class
  exception Unsat of var * var * var list
  val repr : 'a eq_class -> var
  val load : 'a eq_class -> 'a
  val create :
    gen:(var -> 'a) -> merge:('a -> 'a -> 'a) ->
    ?callback:('a eq_class -> 'a eq_class -> 'a eq_class -> unit) ->
    section:Util.Section.t -> Backtrack.Stack.t -> 'a t
  val get_class : 'a t -> var -> 'a eq_class
  val find : 'a t -> var -> var
  val add_eq : 'a t -> var -> var -> unit
  val add_neq : 'a t -> var -> var -> unit
  val add_tag : 'a t -> var -> var -> unit
  val find_tag : 'a t -> var -> var * (var * var) option
end

(* Union-find algorithm *)
(* ************************************************************************ *)

module Eq(T : Key) = struct

  module M = Map.Make(T)
  module H = Backtrack.Hashtbl(T)

  type var = T.t

  exception Equal of var * var
  exception Same_tag of var * var
  exception Unsat of var * var * var list

  type 'a eq_class = {
    load : 'a;
    repr : var;
    rank : int;
    tag : (T.t * T.t) option;
    forbidden : (var * var) M.t;
  }

  type 'a node =
    | Follow of var
    | Repr of 'a eq_class

  type 'a t = {
    size : int H.t;
    expl : var H.t;
    table : 'a node H.t;
    gen  : var -> 'a;
    merge : 'a -> 'a -> 'a;
    section : Util.Section.t;
    callback : 'a eq_class -> 'a eq_class -> 'a eq_class -> unit;
  }

  let _callback_default _ _ _ = ()

  let create
      ~gen ~merge
      ?(callback=_callback_default)
      ~section s = {
    section; merge; gen; callback;
    size = H.create s;
    expl = H.create s;
    table = H.create s;
  }

  (* Accessors *)
  let repr (r : _ eq_class) = r.repr
  let load r = r.load

  (* Union-find algorithm with path compression *)
  let find_hash m i default =
    try H.find m i
    with Not_found -> default

  let rec get_class h v =
    match H.find h.table v with
    | Repr r -> r
    | Follow v' ->
      let r = get_class h v' in
      H.add h.table v (Follow r.repr);
      r
    | exception Not_found ->
      let r = {
          repr = v;
          rank = 0;
          tag = None;
          load = h.gen v;
          forbidden = M.empty;
        } in
      H.add h.table v (Repr r);
      r

  let find h x = (get_class h x).repr

  let tag h x v =
    let r = get_class h x in
    let new_m =
      { r with
        tag = match r.tag with
          | Some (_, v') when not (T.equal v v') -> raise (Equal (x, r.repr))
          | (Some _) as t -> t
          | None -> Some (x, v) }
    in
    H.add h.table r.repr (Repr new_m)

  let find_tag h x =
    let r = get_class h x in
    r.repr, r.tag

  let forbid_aux m x =
    try
      let a, b = M.find x m in
      raise (Equal (a, b))
    with Not_found -> ()

  let link h mx my =
    let new_m = {
      repr = mx.repr;
      load = h.merge mx.load my.load;
      rank = if mx.rank = my.rank then mx.rank + 1 else mx.rank;
      tag = (match mx.tag, my.tag with
          | Some (z, t1), Some (w, t2) ->
            if not (T.equal t1 t2) then begin
              Util.debug ~section:h.section "Tag shenanigan:@ @[<hov>%a@ (%a)@ <>@ %a@ (%a)@]"
                T.print t1 T.print z T.print t2 T.print w;
              raise (Equal (z, w))
            end else Some (z, t1)
          | Some t, None | None, Some t -> Some t
          | None, None -> None);
      forbidden = M.merge (fun _ b1 b2 -> match b1, b2 with
          | Some r, _ | None, Some r -> Some r | _ -> assert false)
          mx.forbidden my.forbidden;}
    in
    let aux m z eq =
      match H.find m z with
      | Repr r ->
        let r' =
          { r with
            forbidden = M.add mx.repr eq (M.remove my.repr r.forbidden) }
        in
        H.add m z (Repr r')
      | _ -> assert false
    in
    M.iter (aux h.table) my.forbidden;
    H.add h.table my.repr (Follow mx.repr);
    H.add h.table mx.repr (Repr new_m);
    h.callback mx my new_m

  let union h x y =
    let mx = get_class h x in
    let my = get_class h y in
    if T.compare mx.repr my.repr <> 0 then begin
      forbid_aux mx.forbidden my.repr;
      forbid_aux my.forbidden mx.repr;
      if mx.rank > my.rank then begin
        link h mx my
      end else begin
        link h my mx
      end
    end

  let forbid h x y =
    let mx = get_class h x in
    let my = get_class h y in
    let rx = mx.repr in
    let ry = my.repr in
    if T.compare rx ry = 0 then
      raise (Equal (x, y))
    else match mx.tag, my.tag with
      | Some (a, v), Some (b, v') when T.compare v v' = 0 ->
        raise (Same_tag(a, b))
      | _ ->
        H.add h.table ry (Repr { my with forbidden = M.add rx (x, y) my.forbidden });
        H.add h.table rx (Repr { mx with forbidden = M.add ry (x, y) mx.forbidden })

  (* Equivalence closure with explanation output *)
  let find_parent v m = find_hash m v v

  let rec root m acc curr =
    let parent = find_parent curr m in
    if T.compare curr parent = 0 then
      curr :: acc
    else
      root m (curr :: acc) parent

  let rec rev_root m curr =
    let next = find_parent curr m in
    if T.compare curr next = 0 then
      curr
    else begin
      H.remove m curr;
      let res = rev_root m next in
      H.add m next curr;
      res
    end

  let expl t a b =
    let rec aux last = function
      | x :: r, y :: r' when T.compare x y = 0 ->
        aux (Some x) (r, r')
      | l, l' -> begin match last with
          | Some z -> List.rev_append (z :: l) l'
          | None -> List.rev_append l l'
        end
    in
    aux None (root t.expl [] a, root t.expl [] b)

  let add_eq_aux t i j =
    if T.compare (find t i) (find t j) = 0 then
      ()
    else begin
      let old_root_i = rev_root t.expl i in
      let old_root_j = rev_root t.expl j in
      let nb_i = find_hash t.size old_root_i 0 in
      let nb_j = find_hash t.size old_root_j 0 in
      if nb_i < nb_j then begin
        H.add t.expl i j;
        H.add t.size j (nb_i + nb_j + 1)
      end else begin
        H.add t.expl j i;
        H.add t.size i (nb_i + nb_j + 1)
      end
    end

  (* Functions wrapped to produce explanation in case
   * something went wrong *)
  let add_tag t x v =
    Util.enter_prof t.section;
    match tag t x v with
    | () -> Util.exit_prof t.section
    | exception Equal (a, b) ->
      Util.exit_prof t.section;
      raise (Unsat (a, b, expl t a b))

  let add_eq t i j =
    Util.enter_prof t.section;
    add_eq_aux t i j;
    match union t i j with
    | () -> Util.exit_prof t.section
    | exception Equal (a, b) ->
      Util.exit_prof t.section;
      raise (Unsat (a, b, expl t a b))

  let add_neq t i j =
    Util.enter_prof t.section;
    match forbid t i j with
    | () -> Util.exit_prof t.section
    | exception Equal (a, b) ->
      Util.exit_prof t.section;
      raise (Unsat (a, b, expl t a b))
    | exception Same_tag (x, y) ->
      add_eq_aux t i j;
      let res = expl t i j in
      Util.exit_prof t.section;
      raise (Unsat (i, j, res))

end

