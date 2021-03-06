(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

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
                    (list_of_size (G.oneofl [0;1])
                       (E.Term.make (G.(sized_size (1 -- 100)) @@
                                     E.Term.typed ~config Expr.Ty.prop)))
                    (list_of_size (G.oneofl [0;1])
                       (E.Term.make (G.(sized_size (1 -- 100) @@
                                        E.Term.typed ~config Expr.Ty.prop))))
                    (list_of_size (G.oneofl [0;1]) @@ Unif_test.pair_sized G.(1 -- 100))
                 )
  in
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
  let s = Superposition.empty ~rules section
      ~callback:(fun _ m -> res := m @ !res) in
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
  let s = Superposition.empty ~rules section
      ~callback:(fun _ m -> res := List.fold_right S.add m !res) in
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

let time f =
  let start = Unix.gettimeofday () in
  let res = f () in
  let stop = Unix.gettimeofday () in
  res, stop -. start

let pp_set fmt s =
  Format.fprintf fmt "{@[<hv>%a@]}"
    (fun _ -> S.iter (fun x -> Format.fprintf fmt "@[<hov>%a@]@ " Mapping.print x)) s

let mk_fold name f =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name state
    (fun state ->
       let s, t = time (fun () -> Ext_meta.fold_diff simple S.empty state) in
       let s', t' = time (fun () -> Ext_meta.fold_diff f S.empty state) in
       let ratio = (0.01 +. t) /. (0.01 +. t') in
       if ratio < 0.1 || ratio > 10. then
         QCheck.Test.fail_reportf "Abormal time lag: %f / %f (%f)" t t' ratio;
       if S.equal s s' then true
       else begin
         QCheck.Test.fail_reportf "@[<hv 2>Difference in results:@ ref: %a@ res: %a@]"
           pp_set s pp_set s'
       end
    )

let mk_full name f =
  QCheck.Test.make ~count:10 ~long_factor:100
    ~name state
    (fun state ->
       let s, t = time (fun () -> Ext_meta.fold_diff simple S.empty state) in
       let s', t' = time (fun () -> f state) in
       let ratio = (0.01 +. t) /. (0.01 +. t') in
       if ratio < 0.1 || ratio > 10. then
         QCheck.Test.fail_reportf "Abormal time lag: %f / %f (%f)" t t' ratio;
       if S.equal s s' then true
       else begin
         QCheck.Test.fail_reportf "@[<hv 2>Difference in results:@ ref: %a@ res: %a@]"
           pp_set s pp_set s'
       end
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

