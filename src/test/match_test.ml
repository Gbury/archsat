
open Misc_test.Infix
module E = Expr_test

let section = Section.make "match_test"

(* Substitution generation (no type subst for now) *)
(* ************************************************************************ *)

let print =
  Format.asprintf "%a" Match.print

let small u =
  assert (Expr.Subst.is_empty u.Match.ty_map);
  let aux v t acc = acc + E.Term.small t in
  Expr.Subst.fold aux u.Match.t_map 0

let shrink u =
  let aux (v, t) = I.map (fun t' -> (v, t')) (E.Term.shrink t) in
  let of_list l =
    List.fold_left (fun u (v, t) ->
        Match.bind_term u v t) Match.empty l
  in
  let l = Expr.Subst.bindings u.Match.t_map in
  I.map of_list (S.list ~shrink:aux l)

let sized =
  G.fix (fun self n ->
      if n <= 0 then G.return Match.empty
      else
        G.(
          Misc_test.split_int (n - 1) >>= fun (curr, rest) ->
          self rest >>= fun u ->
          E.Ty.gen >>= fun ty ->
          E.Var.gen ty >>= fun m ->
          E.Term.(typed ~config:{var = 0; meta = 1;} ty) curr >>= fun t ->
          G.return @@ Match.bind_term u m t
        )
    )

let gen = G.sized sized

let make g = QCheck.make ~print ~small ~shrink g

let t = make gen

(* Match tests *)
(* ************************************************************************ *)

let pair =
  let config = E.Term.({var = 1; meta = 0; }) in
  let gen = G.(sized @@ fun size ->
               E.Ty.gen >>= fun ty ->
               E.Term.typed ~config ty size >>= fun a ->
               E.Term.typed ~config ty size >|= fun b -> (a, b)
              ) in
  QCheck.({(pair E.Term.t E.Term.t) with gen = gen })
(* Small hack to get the same printer/shrinker than for pairs, but
   still generate terms of the same type. *)

let match_subst =
  QCheck.Test.make ~count:30 ~long_factor:5
    ~name:"match_subst" pair
    (fun (a, b) ->
       match Match.find ~section a b with
       | None -> QCheck.assume_fail ()
       | Some u ->
         Expr.Term.equal (Match.term_apply u a) b
    )

let subst_match =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"subst_match" (QCheck.pair t E.Term.t)
    (fun (u, pat) ->
       let t = Match.term_apply u pat in
       match Match.find ~section pat t with
       | None -> false
       | Some u' ->
         Expr.Term.equal t (Match.term_apply u' pat)
    )

let match_qtests = [
  match_subst;
  subst_match;
]

let match_tests =
  let open OUnit2 in
  "Match" >:::
  List.map QCheck_runner.to_ounit2_test match_qtests

