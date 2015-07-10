
module A = Builtin.Arith
module M = Map.Make(Expr.Term)

module Mod = struct

  type t = (Z.t * Prime.divisor) list

  let cons x l = x :: l

  let congr k n =
    assert Z.(zero <= k && k < n);
    let l = Prime.decomposition n in
    let l = List.sort (fun d d' -> Z.compare d.Prime.prime d'.Prime.prime) l in
    List.map (fun d -> (Z.erem k (Prime.value d), d)) l

  let rec merge l l' = match l, l' with
    | [], res | res, [] -> Some res
    | (k, d) :: r, (k', d') :: r' ->
      let open Prime in
      begin match Z.compare d.prime d'.prime with
        | 0 ->
          begin match compare d.power d'.power with
            | 0 ->
              if not (Z.equal k k') then None
              else CCOpt.map (cons (k, d)) (merge r r')
            | x when x < 0 ->
              if not (Z.equal (Z.erem k' (value d)) k) then None
              else CCOpt.map (cons (k', d')) (merge r r')
            | _(* x > 0 *) ->
              if not (Z.equal (Z.erem k (value d')) k') then None
              else CCOpt.map (cons (k, d)) (merge r r')
          end
        | x when x < 0 -> CCOpt.map (cons (k, d)) (merge r l')
        | _(* x > 0 *) -> CCOpt.map (cons (k', d')) (merge l r')
      end

  let sum_up l =
    let tot = List.fold_left (fun acc (_, d) ->
        Z.mul acc (Prime.value d)) Z.one l in
    let rem = List.fold_left (fun acc (k, d) ->
        Z.(acc + (k * (divexact tot (Prime.value d))))) Z.zero l in
    rem, tot

end

module Lit = struct
  type t = {
    const : Builtin.Arith.value;
    sum : Q.t M.t;
  }

  let monome coef expr = {
    const = A.Int Z.zero;
    sum = M.singleton expr coef;
  }

  let const c = { const = c; sum = M.empty }

  let zero = const (A.Int (Z.zero))

  let add e f = {
    const = A.add e.const f.const;
    sum = M.merge (fun _ c c' -> match c, c' with
        | Some q, None | None, Some q -> Some q
        | Some q, Some q' -> Some Q.(q + q') | _ -> assert false
      ) e.sum f.sum;
  }

  let times q e = {
    const = A.mul q e.const;
    sum =
      let c = match q with A.Int z -> Q.of_bigint z | A.Rat q -> q | A.Real q -> Lazy.force q in
      M.map (Q.mul c) e.sum;
  }

  let diff a b = add a (times (A.Int Z.(- one)) b)

  let rec parse_num = function
    | { Expr.term = Expr.App ({ Expr.builtin = A.Val v}, [], []) } -> Some (const v)
    | { Expr.term = Expr.App ({ Expr.builtin = A.Op A.Minus}, [], [e]) } ->
      CCOpt.map (times (A.Int Z.(- one))) (parse_num e)
    | { Expr.term = Expr.App ({ Expr.builtin = A.Op A.Sum}, [], l) } ->
      CCOpt.((sequence_l (List.map parse_num l)) >|= List.fold_left add zero)
    | { Expr.term = Expr.App ({ Expr.builtin = A.Op A.Difference}, [], [a; b]) } ->
      CCOpt.map2 diff (parse_num a) (parse_num b)
    | { Expr.term = Expr.App (
        { Expr.builtin =  (A.Op A.Product)}, [],
        ([ { Expr.term = Expr.App ({ Expr.builtin = A.Val v}, [], []) }; e] |
         [ e; { Expr.term = Expr.App ({ Expr.builtin = A.Val v}, [], []) }] ) ) } ->
      CCOpt.map (times v) (parse_num e)
    | { Expr.t_type = { Expr.ty = Expr.TyApp ({ Expr.builtin = A.Type _ }, []) } } as e ->
      Some (monome Q.one e)
    | _ -> None
end
