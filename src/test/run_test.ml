
(* Some dummy tests *)
(* ************************************************************************ *)

let fail =
  QCheck.Test.make ~count:1
    ~name:"dummy_fail" Expr_test.Formula.t
    (fun _ -> false)

let error =
  QCheck.Test.make ~count:1
    ~name:"dummy_error" Expr_test.Term.t
    (fun _ -> raise Not_found)

(* CLI arguments *)
(* ************************************************************************ *)

let long = ref false

let args = Arg.align @@ List.sort
    (fun (s, _, _) (s', _, _) -> compare s s') [
    "-long", Arg.Set long, " enable long tests"
  ]

let anon _ =
  raise (Arg.Bad "Positional arguments are not parsed")

let usage = "./run_test [opts]\tRun the testsuite"

(* Running tests *)
(* ************************************************************************ *)

type counter = {
  start : float;
  expected : int;
  mutable gen : int;
  mutable pass : int;
  mutable fail : int;
  mutable error : int;
}

type res =
  | Res : 'a QCheck.Test.cell * 'a QCheck.TestResult.t -> res

let create cell = {
  start = Util.get_total_time ();
  expected = QCheck.Test.get_count cell;
  gen = 0;
  pass = 0;
  fail = 0;
  error = 0;
}

let pp_counter fmt c =
  let t = Util.get_total_time () -. c.start in
  Format.fprintf fmt "(%4d) %4d ; %4d ; %4d / %4d -- %7.1fs"
    c.gen c.fail c.error c.pass c.expected t

let step c name _ _ r =
  let aux = function
    | QCheck.Test.Success -> c.pass <- c.pass + 1
    | QCheck.Test.Failure -> c.fail <- c.fail + 1
    | QCheck.Test.FalseAssumption -> ()
    | QCheck.Test.Error _ -> c.error <- c.error + 1
  in
  c.gen <- c.gen + 1;
  aux r;
  Format.printf "\r[ ] %a -- %s@?" pp_counter c name

let callback c name _ _ =
  let pass = c.fail = 0 && c.error = 0 in
  Format.printf "\r[%a] %a -- %s@."
    (if pass
     then CCFormat.with_colorf "Green"
     else CCFormat.with_colorf "Red")
    (if pass then "✓" else "✗")
    pp_counter c name

let run_list l =
  let aux = function
    | QCheck.Test.Test cell ->
      let c = create cell in
      let r = QCheck.Test.check_cell ~long:!long
          ~step:(step c) ~call:(callback c) cell in
      Res (cell, r)
  in
  List.map aux l

let print_inst arb x =
  match arb.QCheck.print with
  | Some f -> f x
  | None -> "<no printer>"

let print_fail cell c_ex =
  Format.printf "@\n--- Failure %s@\n@\n" (String.make 68 '-');
  Format.printf "Test %s failed (%d shrink steps):@\n@\n%s@."
    (QCheck.Test.get_name cell) c_ex.QCheck.TestResult.shrink_steps
    (print_inst (QCheck.Test.get_arbitrary cell) c_ex.QCheck.TestResult.instance)

let print_error cell c_ex exn bt =
  Format.printf "@\n=== Error %s\n\n" (String.make 70 '=');
  Format.printf "Test %s errored on (%d shrink steps):@\n@\n%s@\n@\nexception %s@\n%s@."
    (QCheck.Test.get_name cell)
    c_ex.QCheck.TestResult.shrink_steps
    (print_inst (QCheck.Test.get_arbitrary cell) c_ex.QCheck.TestResult.instance)
    (Printexc.to_string exn)
    bt

let analyze_list l =
  let aux = function
    | Res (cell, r) ->
      begin match r.QCheck.TestResult.state with
        | QCheck.TestResult.Success -> ()
        | QCheck.TestResult.Failed l ->
          List.iter (print_fail cell) l
        | QCheck.TestResult.Error (c_ex, exn, bt) ->
          print_error cell c_ex exn bt
      end
  in
  List.iter aux l

(* Main *)
(* ************************************************************************ *)

let run l =
  (* Some options *)
  let () = Printexc.record_backtrace true in
  let () = CCFormat.set_color_default true in
  (* Parsing arguments *)
  let () = Arg.parse args anon usage in
  (* Running tests *)
  let l' = run_list l in
  analyze_list l'

let _ =
  run (
    (* fail :: error :: *)
    Unif_test.unif_qtests @
    Unif_test.match_qtests @
    Unif_test.robinson_qtests @
    Index_test.correct_qtests @
    Index_test.complete_qtests
  )

