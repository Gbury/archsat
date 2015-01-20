
(* TabSat *)


(* Dummy module renaming for extensions *)
module Eq = Eq
module Sat = Sat

(* Types and exceptions *)
exception Out_of_time
exception Out_of_space

type model =
  | None
  | Simple
  | Full

(* Argument parsing *)
let std = Format.std_formatter
let file = ref ""
let p_model = ref None
let p_proof = ref false
let time_limit = ref 300.
let size_limit = ref 1000_000_000.

let int_arg r arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    r := m *. (float_of_string arg1)
  in
  if l = 0 then raise (Arg.Bad "bad numeric argument")
  else
    try
      match arg.[l-1] with
      | 'k' -> multiplier 1e3
      | 'M' -> multiplier 1e6
      | 'G' -> multiplier 1e9
      | 'T' -> multiplier 1e12
      | 's' -> multiplier 1.
      | 'm' -> multiplier 60.
      | 'h' -> multiplier 3600.
      | 'd' -> multiplier 86400.
      | '0'..'9' -> r := float_of_string arg
      | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure "float_of_string" -> raise (Arg.Bad "bad numeric argument")

let setup_gc_stat () =
  at_exit (fun () ->
      Gc.print_stat stdout;
    )

let input_file = fun s -> file := s

let usage = "Usage : main [options] <file>"
let logspec () =
    let res = ref [] in
    Util.Section.iter (fun (name, s) ->
        if name <> "" then
            res := ("-debug." ^ name, Arg.Int (Util.Section.set_debug s),
                    "<lvl> Sets the debug verbose level for section " ^ name) :: !res
        );
    !res

let argspec = Arg.align (List.sort
    (fun (s, _, _) (s', _, _) -> compare s s')
    (Solver.get_options () @ logspec () @ [
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true),
    " Enable stack traces";
    "-debug", Arg.Int Util.set_debug,
    "<lvl> Sets the debug verbose level";
    "-gc", Arg.Unit setup_gc_stat,
    " Outputs statistics about the GC";
    "-i", Arg.String Io.set_input,
    " Sets the input format (default auto)";
    "-model", Arg.Unit (fun () -> p_model := Simple),
    " Print the model found (if sat).";
    "-model-full", Arg.Unit (fun () -> p_model := Full),
    " Print the model found (if sat)(including sub-expressions).";
    "-o", Arg.String Io.set_output,
    " Sets the output format (default none)";
    "-proof", Arg.Set p_proof,
    " Compute and print the proof if unsat.";
    "-size", Arg.String (int_arg size_limit),
    "<s>[kMGT] Sets the size limit for the sat solver";
    "-time", Arg.String (int_arg time_limit),
    "<t>[smhd] Sets the time limit for the sat solver";
    "-x", Arg.String Dispatcher.activate,
    "<name> Activate the given extension";
  ]))

(* Limits alarm *)
let check () =
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > !time_limit then
    raise Out_of_time
  else if s > !size_limit then
    raise Out_of_space

(* Model printing *)
let get_model () =
    List.sort (fun (t, _) (t', _) -> Expr.Term.compare t t')
    (match !p_model with
    | None -> assert false
    | Simple -> Solver.model ()
    | Full -> Solver.full_model ())

(* Logging *)
let start_section s =
    Util.debug 1 "=== %s %s" s (String.make (64 - String.length s) '=')

let end_section () =
    Util.debug 1 "%s" (String.make 69 '=')

(* Main function *)
let main () =
  let _ = Gc.create_alarm check in
  Arg.parse argspec input_file usage;
  if !file = "" then begin
    Arg.usage argspec usage;
    exit 2
  end;

  start_section "parse";
  let cnf = Io.parse_input !file in
  end_section ();

  start_section "pre-process";
  List.iter (List.iter Solver.preprocess) cnf;
  end_section ();

  start_section "assume";
  Solver.assume cnf;
  end_section ();

  start_section "solve";
  let res = Solver.solve () in
  end_section ();

  match res with
  | Solver.Sat ->
    Io.fprintf std "Sat";
    begin match !p_model with
      | None -> () | _ ->
        Io.fprintf std "Model :";
        Io.print_model std (get_model ())
    end
  | Solver.Unsat ->
    Io.fprintf std "Unsat";
    if !p_proof then
      let proof = Solver.get_proof () in
      Io.print_proof std proof
;;

try
  main ()
with
| Io.Syntax_error (l, c, msg) ->
  Format.fprintf std "Syntax error in file %s at line %d, character %d :@\n%s@." !file l c msg;
  exit 2
| Io.Setting_not_found (opt, arg, l) ->
  Format.fprintf std "'%s' is not a valid argument for %s, valid arguments are :@\n%a@."
    arg opt (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) l;
  exit 2
| Dispatcher.Extension_not_found s ->
  Format.fprintf std "Extension '%s' not found. Available extensions are :@\n%a@." s
    (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) (Dispatcher.list_extensions ());
  exit 2
| Dispatcher.Bad_assertion s ->
  Format.fprintf std "%s@." s;
  exit 3


