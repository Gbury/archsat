
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

let seed = ref ~-1
let long = ref false
let only = ref []
let log = ref Format.std_formatter

let set_log s =
  log := Format.formatter_of_out_channel (
      open_out_gen [Open_append] 0x770 s)

let add_only name =
  only := name :: !only

let rand () =
  Random.State.make [| !seed |]

let setup () =
  (* Set random seed *)
  if !seed = -1 then begin
    Random.self_init ();
    seed := Random.int (1 lsl 29)
  end;
  ()

let args = Arg.align @@ List.sort
    (fun (s, _, _) (s', _, _) -> compare s s') [
    "--log", Arg.String set_log, " set file for logging";
    "--long", Arg.Set long, " enable long tests";
    "--only", Arg.String add_only, " run only these tests";
    "--seed", Arg.Set_int seed, " set random seed";
  ]

let anon _ =
  raise (Arg.Bad "Positional arguments are not parsed")

let usage = "./run_test [opts]\tRun the testsuite"

(* Filtering tests *)
(* ************************************************************************ *)

let filter l =
  if !only = [] then l
  else begin
    List.filter (function (QCheck.Test.Test c) ->
        List.mem (QCheck.Test.get_name c) !only
      ) l
  end

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
  expected = begin
    let count = QCheck.Test.get_count cell in
    if !long
    then QCheck.Test.get_long_factor cell * count
    else count
  end;
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
      Format.printf "\r[ ] %a -- %s@?" pp_counter c (QCheck.Test.get_name cell);
      let r = QCheck.Test.check_cell ~long:!long
          ~rand:(rand()) ~step:(step c) ~call:(callback c) cell in
      Res (cell, r)
  in
  Format.printf
    "generated   fail; error; pass / total -     time -- test name\n%!";
  List.map aux l

(* Analyzing test results *)
(* ************************************************************************ *)

let print_inst arb x =
  match arb.QCheck.print with
  | Some f -> f x
  | None -> "<no printer>"

let print_fail cell c_ex =
  Format.fprintf !log "@\n--- Failure %s@\n@\n" (String.make 68 '-');
  Format.fprintf !log "Test %s failed (%d shrink steps):@\n@\n%s@."
    (QCheck.Test.get_name cell) c_ex.QCheck.TestResult.shrink_steps
    (print_inst (QCheck.Test.get_arbitrary cell) c_ex.QCheck.TestResult.instance)

let print_error cell c_ex exn bt =
  Format.fprintf !log "@\n=== Error %s\n\n" (String.make 70 '=');
  Format.fprintf !log "Test %s errored on (%d shrink steps):@\n@\n%s@\n@\nexception %s@\n%s@."
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
  let () = Sys.catch_break true in
  let () = Printexc.record_backtrace true in
  let () = CCFormat.set_color_default true in
  (* Parsing arguments *)
  let () = Arg.parse args anon usage in
  setup ();
  (* Print random seed *)
  Format.fprintf !log "Random seed : %d@." !seed;
  (* Running tests *)
  let l = filter l in
  let l = run_list l in
  analyze_list l

let _ =
  run (
    (* fail :: error :: *)
    Unif_test.unif_qtests @
    Unif_test.robinson_qtests @
    Match_test.match_qtests @
    Index_test.correct_qtests @
    Index_test.complete_qtests @
    Closure_test.closure_qtests
  )

