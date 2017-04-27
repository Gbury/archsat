
open Misc_test.Infix
module E = Expr_test

let section = Section.make "unif_test"

(* Unifier generation (no type subst for now) *)
(* ************************************************************************ *)

let print m = Format.asprintf "%a" Mapping.print m

let small u =
  let aux _ t acc = acc + E.Term.small t in
  Mapping.fold ~term_var:aux ~term_meta:aux u 0

let shrink u =
  let aux (v, t) = I.map (fun t' -> (v, t')) (E.Term.shrink t) in
  let of_list l =
    List.fold_left (fun u (v, t) ->
        Mapping.Meta.bind_term u v t) Mapping.empty l
  in
  let l = Expr.Subst.bindings (Mapping.term_meta u) in
  I.map of_list (S.list ~shrink:aux l)

let sized =
  G.fix (fun self n ->
      if n <= 0 then G.return Mapping.empty
      else
        G.(
          Misc_test.split_int (n - 1) >>= fun (curr, rest) ->
          self rest >>= fun u ->
          E.Ty.gen >>= fun ty ->
          E.Meta.gen ty >>= fun m ->
          E.Term.(typed ~config:{var = 0; meta = 1;} ty) curr >>= fun t ->
          G.return @@ Mapping.Meta.bind_term u m t
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
       Unif.occurs_check (Mapping.fixpoint u)
    )

let fixpoint_proj =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"fixpoint_is_proj" t
    (fun u ->
       QCheck.assume (Unif.occurs_check u);
       let u' = Mapping.fixpoint u in
       Mapping.equal u' (Mapping.fixpoint u')
    )

let unif_qtests = [
  fixpoint_occur;
  fixpoint_proj;
]

let unif_tests =
  let open OUnit2 in
  "Unif" >:::
  List.map QCheck_runner.to_ounit2_test unif_qtests

(* Problem generation *)
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
         Expr.Term.equal (Mapping.apply_term u a) (Mapping.apply_term u b)
    )

let subst_robinson =
  QCheck.Test.make ~count:100 ~long_factor:10
    ~name:"subst_robinson" (QCheck.pair t E.Term.t)
    (fun (u, t) ->
       QCheck.assume (Unif.occurs_check u);
       let t' = Mapping.apply_term u t in
       match Unif.Robinson.find ~section t t' with
       | None -> false
       | Some u' ->
         Unif.occurs_check u' &&
         Expr.Term.equal (Mapping.apply_term u' t) (Mapping.apply_term u' t')
    )

let robinson_qtests = [
  robinson_subst;
  subst_robinson;
]

let robinson_tests =
  let open OUnit2 in
  "Robinson" >:::
  List.map QCheck_runner.to_ounit2_test robinson_qtests


