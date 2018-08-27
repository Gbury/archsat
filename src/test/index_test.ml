(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make "index_test"

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

let pb_match =
  let config = Expr_test.Term.({ var = 1; meta = 1; }) in
  let term = Expr_test.Term.(make @@ gen_c config) in
  QCheck.(pair term (list (pair term int)))

let pb_unif =
  let config = Expr_test.Term.({ var = 0; meta = 1; }) in
  let term = Expr_test.Term.(make @@ gen_c config) in
  QCheck.(pair term (list (pair term int)))

let fold f l acc =
  List.fold_left (fun acc (key, value) -> f key value acc) acc l

(* Correctness check *)
(* ************************************************************************ *)

let naive_correct_equal =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"naive_correct_equal" pb_match
    (fun (pat, l) ->
       let t = fold N.add l (N.empty section) in
       List.for_all (fun (t, _) ->
           Expr.Term.equal t pat)
         (N.find_equal pat t)
    )

let naive_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"naive_correct_match" pb_match
    (fun (pat, l) ->
       let t = fold N.add l (N.empty section) in
       List.for_all (fun (t, u, _) ->
           Expr.Term.equal t (Mapping.apply_term ~fix:false u pat))
         (N.find_match pat t)
    )

let naive_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"naive_correct_unify" pb_unif
    (fun (pat, l) ->
       let t = fold N.add l (N.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Mapping.apply_term u t) (Mapping.apply_term u pat))
         (N.find_unify pat t)
    )

let index_correct_equal =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"index_correct_equal" pb_match
    (fun (pat, l) ->
       let t = fold I.add l (I.empty ~key:[] section) in
       List.for_all (fun (t, _) ->
           Expr.Term.equal t pat)
         (I.find_equal pat t)
    )

let index_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"index_correct_match" pb_match
    (fun (pat, l) ->
       let t = fold I.add l (I.empty ~key:[] section) in
       List.for_all (fun (t, u, _) ->
           Expr.Term.equal t (Mapping.apply_term ~fix:false u pat))
         (I.find_match pat t)
    )

let index_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"index_correct_unify" pb_unif
    (fun (pat, l) ->
       let t = fold I.add l (I.empty ~key:[] section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Mapping.apply_term u t) (Mapping.apply_term u pat))
         (I.find_unify pat t)
    )

let fingerprint_correct_equal =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"fingerprint_correct_equal" pb_match
    (fun (pat, l) ->
       let t = fold I.add l (I.empty section) in
       List.for_all (fun (t, _) ->
           Expr.Term.equal t pat)
         (I.find_equal pat t)
    )

let fingerprint_correct_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"fingerprint_correct_match" pb_match
    (fun (pat, l) ->
       let t = fold I.add l (I.empty section) in
       List.for_all (fun (t, u, _) ->
           Expr.Term.equal t (Mapping.apply_term ~fix:false u pat))
         (I.find_match pat t)
    )

let fingerprint_correct_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name:"fingerprint_correct_unify" pb_unif
    (fun (pat, l) ->
       let t = fold I.add l (I.empty section) in
       List.for_all (fun (t, u, _) ->
           Unif.occurs_check u &&
           Expr.Term.equal (Mapping.apply_term u t) (Mapping.apply_term u pat))
         (I.find_unify pat t)
    )

let correct_qtests = [
  (* naive index *)
  naive_correct_equal;
  naive_correct_match;
  naive_correct_unify;
  (* bare index (no fingerprint actually usedà *)
  index_correct_equal;
  index_correct_match;
  index_correct_unify;
  (* full ingerprinted index *)
  fingerprint_correct_equal;
  fingerprint_correct_match;
  fingerprint_correct_unify;
]

(* Completeness check *)
(* ************************************************************************ *)

let eq_unif res1 res2 =
  let cmp (t, _, _) (t', _, _) = Expr.Term.compare t t' in
  let l1 = List.sort cmp res1 in
  let l2 = List.sort cmp res2 in
  CCList.equal (fun (t, u, l) (t', u', l') ->
      Expr.Term.equal t t' &&
      Mapping.equal u u' &&
      CCList.equal (=) l l') l1 l2

let eq_match res1 res2 =
  let cmp (t, _, _) (t', _, _) = Expr.Term.compare t t' in
  let l1 = List.sort cmp res1 in
  let l2 = List.sort cmp res2 in
  CCList.equal (fun (t, u, l) (t', u', l') ->
      Expr.Term.equal t t' &&
      Mapping.equal u u' &&
      CCList.equal (=) l l') l1 l2

let eq_equal res1 res2 =
  let cmp (t, _) (t', _) = Expr.Term.compare t t' in
  let l1 = List.sort cmp res1 in
  let l2 = List.sort cmp res2 in
  CCList.equal (fun (t, l) (t', l') ->
      Expr.Term.equal t t' &&
      CCList.equal (=) l l') l1 l2

(* We assume here that the naive implementation is complete. *)

let index_complete_equal =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "index_complete_equal" pb_match
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty ~key:[] section) in
       eq_equal (N.find_equal pat ref) (I.find_equal pat t)
    )

let index_complete_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "index_complete_match" pb_match
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty ~key:[] section) in
       eq_match (N.find_match pat ref) (I.find_match pat t)
    )

let index_complete_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "index_complete_unify" pb_unif
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty ~key:[] section) in
       eq_unif (N.find_unify pat ref) (I.find_unify pat t)
    )

let fingerprint_complete_equal =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "fingerprint_complete_equal" pb_match
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty section) in
       eq_equal (N.find_equal pat ref) (I.find_equal pat t)
    )

let fingerprint_complete_match =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "fingerprint_complete_match" pb_match
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty section) in
       eq_match (N.find_match pat ref) (I.find_match pat t)
    )

let fingerprint_complete_unify =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name: "fingerprint_complete_unify" pb_unif
    (fun (pat, l) ->
       let ref = fold N.add l (N.empty section) in
       let t = fold I.add l (I.empty section) in
       eq_unif (N.find_unify pat ref) (I.find_unify pat t)
    )

let complete_qtests = [
  index_complete_equal;
  index_complete_match;
  index_complete_unify;
  fingerprint_complete_equal;
  fingerprint_complete_match;
  fingerprint_complete_unify;
]



