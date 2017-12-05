
open Misc_test.Infix
module E = Expr_test
module S = Set.Make(Mapping)

let section = Section.make "meta_test"

(* Problem generation *)
(* ************************************************************************ *)

(* Meta state problem without equalities *)
let state =
  let config = E.Term.({var = 0; meta = 1; }) in
  let rev state =
    state.Ext_meta.true_preds,
    state.Ext_meta.false_preds,
    state.Ext_meta.inequalities
  in
  let conv (true_preds, false_preds, inequalities) =
    Ext_meta.{ true_preds; false_preds; inequalities;
               equalities = []; formulas = []; }
  in
  let a = QCheck.(triple
                   (list (E.Term.make (G.sized @@ E.Term.typed ~config Expr.Ty.prop)))
                   (list (E.Term.make (G.sized @@ E.Term.typed ~config Expr.Ty.prop)))
                   (list Unif_test.pair)) in
  QCheck.map ~rev conv a

(* High-level meta unification *)
(* ************************************************************************ *)

let robinson t t' =
  match Unif.Robinson.term Mapping.empty t t' with
  | m -> Some m
  | exception Unif.Robinson.Impossible_ty _ -> None
  | exception Unif.Robinson.Impossible_term _ -> None

let simple acc t t' =
  match robinson t t' with
  | Some m -> S.add m acc
  | None -> acc

let simple_cached () =
  let cache = Unif.Cache.create () in
  (fun acc t t' ->
     match Unif.Cache.with_cache cache robinson t t' with
     | Some m -> S.add m acc
     | None -> acc)

let super_each rules =
  let res = ref [] in
  let s = Superposition.empty ~rules section (fun m -> res := m :: !res) in
  (fun acc t t' ->
     let _ = Superposition.solve (Superposition.add_neq s t t') in
     match !res with
     | [] -> acc
     | [m] -> res := []; S.add m acc
     | l -> QCheck.Test.fail_reportf
              "@[<hv 2>More than one unifier for pair:@ %a@ <>@ %a@ ->@ @[<hv>%a@]@]"
              Expr.Print.term t Expr.Print.term t'
              CCFormat.(list ~sep:(return "@ ") Mapping.print) l
  )

let super_all rules state =
  let res = ref S.empty in
  let s = Superposition.empty ~rules section (fun m -> res := S.add m !res) in
  let s' = Ext_meta.fold_diff (fun acc a b -> Superposition.add_neq acc a b) s state in
  let _ = Superposition.solve s' in
  !res

let super_each_no_simplif_unif =
  super_each Superposition.{ er = true; sn = true; sp = true;
                             es = false; rp = false; rn = false;
                             mn = false; mp = false; }
let super_each_simplif_unif =
  super_each Superposition.{ er = true; sn = true; sp = true;
                             es = true; rp = true; rn = true;
                             mn = true; mp = true; }
let super_all_no_simplif_unif =
  super_all Superposition.{ er = true; sn = true; sp = true;
                            es = false; rp = false; rn = false;
                            mn = false; mp = false; }
let super_all_simplif_unif =
  super_all Superposition.{ er = true; sn = true; sp = true;
                            es = true; rp = true; rn = true;
                            mn = true; mp = true; }

(* Actual tests *)
(* ************************************************************************ *)

let mk_fold name f =
  QCheck.Test.make ~count:1 ~long_factor:1000
    ~name state
    (fun state ->
       let s = Ext_meta.fold_diff simple S.empty state in
       let s' = Ext_meta.fold_diff f S.empty state in
       S.equal s s'
    )

let mk_full name f =
  QCheck.Test.make ~count:1 ~long_factor:1000
    ~name state
    (fun state ->
       let s = Ext_meta.fold_diff simple S.empty state in
       let s' = f state in
       S.equal s s'
    )


let cached_robinson = mk_fold "cached_robinson" (simple_cached ())
let super_each_simplif = mk_fold "super_each_simplif" super_each_simplif_unif
let super_each_no_simplif = mk_fold "super_each_no_simplif" super_each_no_simplif_unif
let super_all_simplif = mk_full "super_all_simplif" super_all_simplif_unif
let super_all_no_simplif = mk_full "super_all_no_simplif" super_all_no_simplif_unif

let meta_qtests = [
  cached_robinson;
  super_each_simplif;
  super_each_no_simplif;
  super_all_simplif;
  super_all_no_simplif;
]

