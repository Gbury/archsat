
module type S = sig
  type t
  type var

  exception Unsat of var * var * var list

  val empty : t
  val find : t -> var -> var
  val add_eq : t -> var -> var -> t
  val add_neq : t -> var -> var -> t
end

module Make(T : Map.OrderedType) = struct

  module M = Map.Make(T)

  type var = T.t

  exception Equal of var * var
  exception Unsat of var * var * var list

  type repr_info = {
    mutable rank : int;
    mutable forbidden : (var * var) M.t;
  }

  type node =
    | Follow of var
    | Repr of repr_info

  type t = {
      size : int M.t;
      expl : var M.t;
      mutable repr : node M.t;
  }

  let empty = { size = M.empty; expl = M.empty; repr = M.empty }

  (* Union-find algorithm with path compression *)
  let self_repr = Repr { rank = 0; forbidden = M.empty }

  let find_map m i default =
    try M.find i m
    with Not_found -> default

  let rec find_aux m i =
      match find_map m i self_repr with
      | Repr r -> m, r, i
      | Follow j ->
        let m', r, k = find_aux m j in
        M.add i (Follow k) m', r, k

  let get_repr h x =
      let m, r, y = find_aux h.repr x in
      h.repr <- m;
      y, r

  let find h x = fst (get_repr h x)

  let forbid_aux m x =
      try
          let a, b = M.find x m in
          raise (Equal (a, b))
      with Not_found -> ()

  let link h x mx y my =
    let mx = {
        rank = if mx.rank = my.rank then mx.rank + 1 else mx.rank;
        forbidden = M.merge (fun _ b1 b2 -> match b1, b2 with
            | Some r, _ | None, Some r -> Some r | _ -> assert false)
            mx.forbidden my.forbidden;
    } in
    let aux z eq m =
        match M.find z m with
        | Repr r ->
          let r' = { r with
            forbidden = M.add x eq (M.remove y r.forbidden) }
          in
          M.add z (Repr r') m
        | _ -> assert false
    in
    let map = M.fold aux my.forbidden h.repr in
    { h with repr = M.add x (Repr mx)
        (M.add y (Follow x) map) }

  let union h x y =
    let rx, mx = get_repr h x in
    let ry, my = get_repr h y in
    if T.compare rx ry <> 0 then begin
        forbid_aux mx.forbidden ry;
        forbid_aux my.forbidden rx;
        if mx.rank > my.rank then
            link h rx mx ry my
        else
            link h ry my rx mx
    end else
        h

  let forbid h x y =
    let rx, mx = get_repr h x in
    let ry, my = get_repr h y in
    if T.compare rx ry = 0 then
        raise (Equal (x, y))
    else
        { h with repr =
            M.add rx (Repr { mx with forbidden = M.add ry (x, y) mx.forbidden })
           (M.add ry (Repr { my with forbidden = M.add rx (x, y) mx.forbidden }) h.repr) }

  (* Equivalence closure with explanation output *)
  let find_parent v m = find_map m v v

  let rev_root m root =
    let rec aux m curr next =
      if T.compare curr next = 0 then
        m, curr
      else
        let parent = find_parent next m in
        let m' = M.add next curr (M.remove curr m) in
        aux m' next parent
    in
    aux m root (find_parent root m)

  let rec root m acc curr =
    let parent = find_parent curr m in
    if T.compare curr parent = 0 then
      curr :: acc
    else
      root m (curr :: acc) parent

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
      t
    else
      let m, old_root_i = rev_root t.expl i in
      let m, old_root_j = rev_root m j in
      let nb_i = find_map t.size old_root_i 0 in
      let nb_j = find_map t.size old_root_j 0 in
      if nb_i < nb_j then {
        repr = t.repr;
        expl = M.add i j m;
        size = M.add j (nb_i + nb_j + 1) t.size; }
      else {
        repr = t.repr;
        expl = M.add j i m;
        size = M.add i (nb_i + nb_j + 1) t.size; }

  let add_eq t i j =
    let t' = add_eq_aux t i j in
    try
      union t' i j
    with Equal (a, b) ->
      raise (Unsat (a, b, expl t' a b))

  let add_neq t i j =
    try
      forbid t i j
    with Equal (a, b) ->
      raise (Unsat (a, b, expl t a b))

  let are_neq t a b =
    try
      ignore (union t a b);
      false
    with Equal _ ->
      true

end
