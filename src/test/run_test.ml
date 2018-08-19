(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Main *)
(* ************************************************************************ *)

let () =
  (* Set better margins *)
  Format.set_margin 200;
  (* Some options *)
  let () = Sys.catch_break true in
  QCheck_runner.run_tests_main (
    Unif_test.unif_qtests @
    Unif_test.robinson_qtests @
    Match_test.match_qtests @
    Index_test.correct_qtests @
    Index_test.complete_qtests @
    Closure_test.closure_qtests @
    Meta_test.meta_qtests
  )

