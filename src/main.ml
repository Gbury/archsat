
(* TabSat *)

(* Dummy module renaming for extensions *)
module Eq = Eq
module Tab = Tab
module Prop = Prop
module Functions = Functions

module Tau = Tau
module Meta = Meta

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
let p_type_only = ref false
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

let arg_compare (s, _, _) (s', _, _) = String.compare s s'

let pp_string b s = Printf.bprintf b "%s" s

let argspec = Arg.align (List.sort arg_compare
    (Solver.get_options () @ logspec () @ [
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true),
    " Enable stack traces";
    "-debug", Arg.Int Util.set_debug,
    "<lvl> Sets the debug verbose level";
    "-gc", Arg.Unit setup_gc_stat,
    " Outputs statistics about the GC";
    "-i", Arg.String Io.set_input,
    Util.sprintf " Sets the input format (default auto)(available are : %a)"
        (Util.pp_list ~sep:", " pp_string) Io.accepted_input;
    "-model", Arg.Unit (fun () -> p_model := Simple),
    " Print the model found (if sat).";
    "-model-full", Arg.Unit (fun () -> p_model := Full),
    " Print the model found (if sat)(including sub-expressions).";
    "-o", Arg.String Io.set_output,
    Util.sprintf " Sets the output format (default standard)(available are : %a)"
        (Util.pp_list ~sep:", " pp_string) Io.accepted_output;
    "-proof", Arg.Set p_proof,
    " Compute and print the proof if unsat.";
    "-size", Arg.String (int_arg size_limit),
    "<s>[kMGT] Sets the size limit for the sat solver";
    "-time", Arg.String (int_arg time_limit),
    "<t>[smhd] Sets the time limit for the sat solver";
    "-type-only", Arg.Set p_type_only,
    " Only parse and type the given problem. Do not attempt to solve.";
    "-x", Arg.String Dispatcher.set_exts,
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

let end_section () = ()
    (* Util.debug 1 "%s" (String.make 69 '=') *)

let wrap s f x =
    start_section s;
    let res = f x in
    end_section ();
    res

(* Execute given command *)
let do_command = function
  | Ast.Sat cnf ->
    if not !p_type_only then
        wrap "assume" Solver.assume cnf
  | Ast.NewType (name, s, n) ->
    wrap ("typing " ^ name) Type.new_type_def (s, n)
  | Ast.TypeDef (name, s, t) ->
    wrap ("typing " ^ name) Type.new_const_def (s, t)
  | Ast.Assert (name, t) ->
    let f = wrap ("typing " ^ name) Type.parse t in
    if not !p_type_only then
      wrap "assume" Solver.assume [[f]]
  | Ast.CheckSat ->
    if not !p_type_only then
      let res = wrap "solve" Solver.solve () in
      begin match res with
        | Solver.Sat ->
          Io.print_res std "Sat" (Sys.time ());
          begin match !p_model with
            | None -> () | _ ->
              Io.fprintf std "Model :";
              Io.print_model std (get_model ())
          end
        | Solver.Unsat ->
          Io.print_res std "Unsat" (Sys.time ());
          if !p_proof then
            let proof = Solver.get_proof () in
            Io.print_proof std proof
      end
  | c ->
    Io.fprintf std "%a : operation not supported yet" Ast.print_command_name c;
    exit 2

(* Main function *)
let main () =
  let _ = Gc.create_alarm check in
  (* Default extensions *)
  Dispatcher.set_exts "+eq,+uf,+tab,+prop,+tau,+meta";
  (* Argument parsing *)
  Arg.parse argspec input_file usage;
  if !file = "" then begin
    Arg.usage argspec usage;
    exit 2
  end;
  (* Input file parsing *)
  let commands = wrap "parse" Io.parse_input !file in
  (* Commands execution *)
  Queue.iter do_command commands
;;

try
  main ()
with
| Out_of_time ->
  Io.print_res std "Timeout" (Sys.time ());
  exit 1
| Out_of_space ->
  Io.print_res std "Out of space" (Sys.time ());
  exit 1
| Io.Parsing_error (l, msg) ->
  Format.fprintf std "%a:@\n%s@." ParseLocation.fmt l msg;
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


