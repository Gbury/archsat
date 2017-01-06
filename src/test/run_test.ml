
let _ =
  let open OUnit2 in
  run_test_tt_main
    ("tests" >::: [
        Unif_test.unif_tests;
        Unif_test.match_tests;
        Unif_test.robinson_tests;
        Index_test.correct_tests;
        Index_test.complete_tests;
      ]
    )

