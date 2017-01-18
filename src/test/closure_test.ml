
let section = Util.Section.make "closure_test"

(* Problem generation *)
(* ************************************************************************ *)

let chain =
  let config = Expr_test.Term.{ var = 0; meta = 0; } in
  let aux ty self n =
    QCheck.Gen.(
      if n <= 0 then return [] else
      Misc_test.split_int n >>= fun (a, b) ->
      map2 CCList.cons (Expr_test.Term.typed ~config ty a) (self b)
    ) in
  QCheck.Gen.(
    Expr_test.Ty.gen >>= fun ty ->
    sized (fix (aux ty))
  )

let pairify l =
  let rec aux acc = function
    | [_] | [] -> acc
    | a :: ((b :: _) as r) ->
      aux ((a, b) :: acc) r
  in
  aux [] l

let pb =
  let gen =
    QCheck.Gen.(
      list chain >>= fun eqs ->
      Misc_test.sublist (List.concat eqs) >>= fun neqs ->
      let l = List.map (fun x -> (true, x))
          (CCList.flat_map pairify eqs) in
      let l' = List.map (fun x -> (false, x)) (pairify neqs) in
      shuffle_l (l @ l')
    ) in
  QCheck.{
    (list (pair bool (pair Expr_test.Term.t Expr_test.Term.t)))
    with QCheck.gen = gen
  }

(* Naive solving *)
(* ************************************************************************ *)

module S = Set.Make(Expr.Term)
module H = Hashtbl.Make(Expr.Term)

type t = { mutable eq : S.t }

let find h t =
  match H.find h t with
  | eq -> eq
  | exception Not_found ->
    let ht = { eq = S.singleton t } in
    H.add h t ht;
    ht

let make l =
  let h = H.create 42 in
  let aux (a, b) =
    let ha = find h a in
    ha.eq <- S.add b ha.eq;
    let hb = find h b in
    hb.eq <- S.add a hb.eq;
    ()
  in
  List.iter aux l;
  h

let compile l =
  let eq, neq = CCList.partition_map (function
      | (true, p) -> `Left p
      | (false, p) -> `Right p) l in
  let t = make eq in
  t, neq

let all_eq h t =
  let rec aux curr todo =
    if S.is_empty todo then curr
    else begin
      let a = S.choose todo in
      let s = find h a in
      let s' = S.diff s.eq curr in
      aux (S.union curr s') (S.union s' (S.remove a todo))
    end
  in
  aux S.empty (S.singleton t)

let sat l =
  let t, neq = compile l in
  List.for_all (fun (a, b) -> not (S.mem a (all_eq t b))) neq

let check_proof l (a, b, chain) =
  let t, neq = compile l in
  List.exists (fun (c, d) ->
      Expr.Term.((equal a c && equal b d) ||
                 (equal a d && equal b c))) neq &&
  List.for_all (fun (c, d) -> S.mem d (find t c).eq) (pairify chain) &&
  CCOpt.map_or ~default:false (Expr.Term.equal a) (CCList.head_opt chain) &&
  CCOpt.map_or ~default:false (Expr.Term.equal b) (CCList.last_opt chain)

(* Checking Closure *)
(* ************************************************************************ *)

module C = Closure.Eq(Expr.Term)

let mk_closure l =
  let gen _ = () and merge () () = () in
  let t = C.create ~gen ~merge ~section
      (Backtrack.Stack.create section) in
  List.iter (function
      | (true, (a, b)) -> C.add_eq t a b
      | (false, (a, b)) -> C.add_neq t a b) l

let closure_sat =
  QCheck.Test.make ~count:1 ~long_factor:100
    ~name:"closure_sat" pb
    (fun l ->
       QCheck.assume (sat l);
       try mk_closure l; true
       with C.Unsat _ -> false
    )

let closure_unsat =
  QCheck.Test.make ~count:10 ~long_factor:10
    ~name:"closure_unsat" pb
    (fun l ->
       QCheck.assume (not (sat l));
       try mk_closure l; false
       with C.Unsat (a, b, chain) -> check_proof l (a, b, chain)
    )

let closure_check =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"closure_check" pb
    (fun l ->
       try
         mk_closure l;
         sat l
       with C.Unsat (a, b, chain) ->
         check_proof l (a, b, chain))

let closure_qtests = [
  closure_sat;
  closure_unsat;
  closure_check;
]

let closure_tests =
  let open OUnit2 in
  "Closure" >:::
  List.map QCheck_runner.to_ounit2_test closure_qtests



