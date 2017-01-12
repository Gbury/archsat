
let section = Util.Section.make "index_test"

(* Module definitions and initialisation *)
(* ************************************************************************ *)

module Int = struct
  type t = int
  let compare = compare
end

module N = Index.Simple(Int)
module I = Index.Make(Int)

(* Problem generation *)
(* ************************************************************************ *)

let pb =
  QCheck.(pair (Expr_test.Term.t) (list (pair Expr_test.Term.t int)))

let fold f l acc =
  List.fold_left (fun acc (key, value) -> f key value acc) acc l

(* Correctness check *)
(* ************************************************************************ *)

let naive_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"naive_correct_match" pb
    (fun (pat, l) ->
       let t = fold N.add l (N.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal t (Unif.term_subst u pat))
         (N.find_match pat t)
    )

let naive_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"naive_correct_unify" pb
    (fun (pat, l) ->
       let t = fold N.add l (N.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Unif.term_subst u t) (Unif.term_subst u pat))
         (N.find_unify pat t)
    )

let index_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"index_correct_match" pb
    (fun (pat, l) ->
       let t = fold I.add l (I.empty ~key:[] section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal t (Unif.term_subst u pat))
         (I.find_match pat t)
    )

let index_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"index_correct_unify" pb
    (fun (pat, l) ->
       let t = fold I.add l (I.empty ~key:[] section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Unif.term_subst u t) (Unif.term_subst u pat))
         (I.find_unify pat t)
    )

let fingerprint_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"fingerprint_correct_match" pb
    (fun (pat, l) ->
       let t = fold I.add l (I.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal t (Unif.term_subst u pat))
         (I.find_match pat t)
    )

let fingerprint_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"fingerprint_correct_unify" pb
    (fun (pat, l) ->
       let t = fold I.add l (I.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Unif.term_subst u t) (Unif.term_subst u pat))
         (I.find_unify pat t)
    )

let correct_qtests = [
  naive_correct_match;
  naive_correct_unify;
  index_correct_match;
  index_correct_unify;
  fingerprint_correct_match;
  fingerprint_correct_unify;
]

let correct_tests =
  let open OUnit2 in
  "Index_correct" >:::
  List.map QCheck_runner.to_ounit2_test correct_qtests

(* Completeness check *)
(* ************************************************************************ *)

let eq_results res1 res2 =
  let cmp (t, _, _) (t', _, _) = Expr.Term.compare t t' in
  let l1 = List.sort cmp res1 in
  let l2 = List.sort cmp res2 in
  CCList.equal (fun (t, u, l) (t', u', l') ->
      Expr.Term.equal t t' &&
      Unif.equal u u' &&
      CCList.equal (=) l l') l1 l2

(* We assume here that the naive implementation is complete. *)

let index_complete_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "index_complete_match" pb
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty ~key:[] section) in
       eq_results (N.find_match pat ref) (I.find_match pat t)
    )

let index_complete_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "index_complete_unify" pb
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty ~key:[] section) in
       eq_results (N.find_unify pat ref) (I.find_unify pat t)
    )

let fingerprint_complete_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "fingerprint_complete_match" pb
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty section) in
       eq_results (N.find_match pat ref) (I.find_match pat t)
    )

let fingerprint_complete_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "fingerprint_complete_unify" pb
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty section) in
       eq_results (N.find_unify pat ref) (I.find_unify pat t)
    )

let complete_qtests = [
  index_complete_match;
  index_complete_unify;
  fingerprint_complete_match;
  fingerprint_complete_unify;
]

let complete_tests =
  let open OUnit2 in
  "Index_complete" >:::
  List.map QCheck_runner.to_ounit2_test complete_qtests


