
open Misc_test.Infix
module E = Expr_test

let section = Util.Section.make "unif_test"

(* Unifier generation (no type subst for now) *)
(* ************************************************************************ *)

let print =
  Format.asprintf "%a" Unif.print

let small u =
  assert (Expr.Subst.is_empty u.Unif.ty_map);
  let aux v t acc = acc + E.Term.small t in
  Expr.Subst.fold aux u.Unif.t_map 0

let shrink u =
  let aux (v, t) = I.map (fun t' -> (v, t')) (E.Term.shrink t) in
  let of_list l =
    List.fold_left (fun u (v, t) ->
        Unif.bind_term u v t) Unif.empty l
  in
  let l = Expr.Subst.bindings u.Unif.t_map in
  I.map of_list (S.list ~shrink:aux l)

let sized =
  G.fix (fun self n ->
      if n <= 0 then G.return Unif.empty
      else
        G.(
          Misc_test.split_int (n - 1) >>= fun (curr, rest) ->
          self rest >>= fun u ->
          E.Ty.gen >>= fun ty ->
          E.Meta.gen ty >>= fun m ->
          E.Term.(typed ~config:{var = 0; meta = 1;} ty) curr >>= fun t ->
          G.return @@ Unif.bind_term u m t
        )
    )

let gen = G.sized sized

let make g = QCheck.make ~print ~small ~shrink g

let t = make gen

(* Unifiers tests *)
(* ************************************************************************ *)

let fixpoint_occur =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"fixpoint_occur" t
    (fun u ->
       QCheck.assume (Unif.occurs_check u);
       Unif.occurs_check (Unif.fixpoint u)
    )

let fixpoint_proj =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"fixpoint_is_proj" t
    (fun u ->
       QCheck.assume (Unif.occurs_check u);
       let u' = Unif.fixpoint u in
       Unif.equal u' (Unif.fixpoint u')
    )

let unif_qtests = [
  fixpoint_occur;
  fixpoint_proj;
]

let unif_tests =
  let open OUnit2 in
  "Unif" >:::
  List.map QCheck_runner.to_ounit2_test unif_qtests

(* Match tests *)
(* ************************************************************************ *)

let pair =
  let config = E.Term.({var = 0; meta = 1; }) in
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
       match Unif.Match.find ~section a b with
       | None -> QCheck.assume_fail ()
       | Some u ->
         Unif.occurs_check u &&
         Expr.Term.equal a (Unif.term_subst u b)
    )

let subst_match =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"subst_match" (QCheck.pair t E.Term.t)
    (fun (u, pat) ->
       QCheck.assume (Unif.occurs_check u);
       let t = Unif.term_subst u pat in
       match Unif.Match.find ~section t pat with
       | None -> false
       | Some u' ->
         Unif.occurs_check u' &&
         Expr.Term.equal t (Unif.term_subst u' pat)
    )

let match_qtests = [
  match_subst;
  subst_match;
]

let match_tests =
  let open OUnit2 in
  "Match" >:::
  List.map QCheck_runner.to_ounit2_test match_qtests

(* Robinson unification tests *)
(* ************************************************************************ *)

let robinson_subst =
  QCheck.Test.make ~count:30 ~long_factor:5
    ~name:"robinson_subst" pair
    (fun (a, b) ->
       match Unif.Robinson.find ~section a b with
       | None -> QCheck.assume_fail ()
       | Some u ->
         Unif.occurs_check u &&
         Expr.Term.equal (Unif.term_subst u a) (Unif.term_subst u b)
    )

let subst_robinson =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"subst_robinson" (QCheck.pair t E.Term.t)
    (fun (u, t) ->
       QCheck.assume (Unif.occurs_check u);
       let t' = Unif.term_subst u t in
       match Unif.Robinson.find ~section t t' with
       | None -> false
       | Some u' ->
         Unif.occurs_check u' &&
         Expr.Term.equal (Unif.term_subst u' t) (Unif.term_subst u' t')
    )

let robinson_qtests = [
  robinson_subst;
  subst_robinson;
]

let robinson_tests =
  let open OUnit2 in
  "Robinson" >:::
  List.map QCheck_runner.to_ounit2_test robinson_qtests


