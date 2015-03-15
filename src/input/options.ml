
open Cmdliner

(* Type definitions for common options *)
type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

type output =
  | Standard
  | Dot

type model =
  | NoModel
  | Simple
  | Full

type copts = {
  (* Input/Output option *)
  formatter : Format.formatter;
  input_file : string;
  input_format : input;
  output_format : output;

  (* Proving options *)
  proof : bool;
  solve : bool;
  extensions : string list;

  (* Printing options *)
  print_proof : out_channel option;
  print_model : model;

  (* Limits *)
  time_limit : float;
  size_limit : float;
}

let mk_opts bt quiet log debug file input output proof type_only exts p_proof p_model time size =
  if bt then
    Printexc.record_backtrace true;
  (* Set up debug levels *)
  if quiet then
    Util.Section.clear_debug Util.Section.root
  else begin
    Util.set_debug log;
    List.iter (fun (s, lvl) -> Util.Section.set_debug s lvl) debug
  end;
  (* Global options record *)
  {
    formatter = Format.std_formatter;
    input_file = file;
    input_format = input;
    output_format = output;

    proof = proof || (p_proof <> None);
    solve = not type_only;
    extensions = List.concat exts;

    print_model = p_model;
    print_proof = (match p_proof with | Some s -> Some (open_out s) | None -> None);

    time_limit = time;
    size_limit = size;
  }

let clean opt =
  match opt.print_proof with Some out -> close_out out | None -> ()

(* Argument converter for integer with multiplier suffix *)
let nb_sec_minute = 60
let nb_sec_hour = 60 * nb_sec_minute
let nb_sec_day = 24 * nb_sec_hour

let time_string f =
  let n = int_of_float f in
  let aux n div = n / div, n mod div in
  let n_day, n = aux n nb_sec_day in
  let n_hour, n = aux n nb_sec_hour in
  let n_min, n = aux n nb_sec_minute in
  let print_aux s n = if n <> 0 then (string_of_int n) ^ s else "" in
  (print_aux "d" n_day) ^
  (print_aux "h" n_hour) ^
  (print_aux "m" n_min) ^
  (print_aux "s" n)

let print_time fmt f = Format.fprintf fmt "%s" (time_string f)

let parse_time arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    `Ok (m *. (float_of_string arg1))
  in
  assert (l > 0);
  try
    match arg.[l-1] with
    | 's' -> multiplier 1.
    | 'm' -> multiplier 60.
    | 'h' -> multiplier 3600.
    | 'd' -> multiplier 86400.
    | '0'..'9' -> `Ok (float_of_string arg)
    | _ -> `Error "bad numeric argument"
  with Failure "float_of_string" -> `Error "bad numeric argument"

let size_string f =
  let n = int_of_float f in
  let aux n div = n / div, n mod div in
  let n_tera, n = aux n 1_000_000_000_000 in
  let n_giga, n = aux n 1_000_000_000 in
  let n_mega, n = aux n 1_000_000 in
  let n_kilo, n = aux n 1_000 in
  let print_aux s n = if n <> 0 then (string_of_int n) ^ s else "" in
  (print_aux "T" n_tera) ^
  (print_aux "G" n_giga) ^
  (print_aux "M" n_mega) ^
  (print_aux "k" n_kilo) ^
  (print_aux "" n)

let print_size fmt f = Format.fprintf fmt "%s" (size_string f)

let parse_size arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    `Ok (m *. (float_of_string arg1))
  in
  assert (l > 0);
  try
    match arg.[l-1] with
    | 'k' -> multiplier 1e3
    | 'M' -> multiplier 1e6
    | 'G' -> multiplier 1e9
    | 'T' -> multiplier 1e12
    | '0'..'9' -> `Ok (float_of_string arg)
    | _ -> `Error "bad numeric argument"
  with Failure "float_of_string" -> `Error "bad numeric argument"

let c_time = parse_time, print_time
let c_size = parse_size, print_size

(* Argument converter for log sections *)
let print_section fmt s = Format.fprintf fmt "%s" (Util.Section.full_name s)
let parse_section arg =
  try `Ok (Util.Section.find arg)
  with Not_found -> `Error ("Invalid debug section '" ^ arg ^ "'")

let section = parse_section, print_section

(* Argument converters for input/output *)
let input_list = [
  "auto", Auto;
  "dimacs", Dimacs;
  "tptp", Tptp;
  "smtlib", Smtlib;
]
let output_list = [
  "standard", Standard;
  "dot", Dot;
]
let model_list = [
  "none", NoModel;
  "simple", Simple;
  "full", Full;
]

let input = Arg.enum input_list
let output = Arg.enum output_list
let model = Arg.enum model_list

(* Argument parsing *)
let copts_sect = "COMMON OPTIONS"
let ext_sect = "ADVANCED OPTIONS"
let help_secs ext_doc = [
  `S copts_sect; `P "Common options for the prover";
  `S "EXTENSIONS"; `P "Available extensions are listed in this section. Each paragraph starts with the extension's name,
 and a description of what the extension does.";
] @ ext_doc @ [
    `S ext_sect; `P "Options primarily used by the extensions (use only if you know what you're doing !).";
    `S "BUGS"; `P "TODO";
  ]

let log_sections () =
  let l = ref [] in
  Util.Section.iter (fun (name, _) -> if name <> "" then l := name :: !l);
  !l

let copts_t () =
  let docs = copts_sect in
  let bt =
      let doc = "Enables printing of backtraces." in
      Arg.(value & flag & info ["b"; "backtrace"] ~docs:ext_sect ~doc)
  in
  let quiet =
    let doc = "Supress all output but the result status of the problem" in
    Arg.(value & flag & info ["q"; "quiet"] ~docs ~doc)
  in
  let log =
    let doc = "Set the global level for debug outpout." in
    Arg.(value & opt int 0 & info ["v"; "verbose"] ~docs ~docv:"LVL" ~doc)
  in
  let debug =
    let doc = Util.sprintf
        "Set the debug level of the given section, as a pair : '$(b,section),$(b,level)'.
        $(b,section) might be %s." (Arg.doc_alts ~quoted:false (log_sections ())) in
    Arg.(value & opt_all (pair section int) [] & info ["debug"] ~docs:ext_sect ~docv:"NAME,LVL" ~doc)
  in
  let file =
    let doc = "Input problem file." in
    Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)
  in
  let input =
    let doc = Util.sprintf
        "Set the format for the input file to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false input_list) in
    Arg.(value & opt input Auto & info ["i"; "input"] ~docs ~docv:"INPUT" ~doc)
  in
  let output =
    let doc = Util.sprintf
        "Set the output for printing results to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false  output_list) in
    Arg.(value & opt output Standard & info ["o"; "output"] ~docs ~docv:"OUTPUT" ~doc)
  in
  let proof =
    let doc = "If set, compute and check the resolution proofs for unsat results. This option
                 does not trigger printing of the proof (see $(b,--proof) option)." in
    Arg.(value & flag & info ["c"; "check"] ~docs ~doc)
  in
  let type_only =
    let doc = "Only parse and type the given problem. Do not attempt to solve." in
    Arg.(value & flag & info ["type-only"] ~docs ~doc)
  in
  let exts =
    let doc = "Activate/deactivate extensions, using their names (see EXTENSIONS section).
                 Prefixing an extension with a $(b,'-') deactivates it, while using only its name
                 (possibly with the $(b,'+') prefix, but not necessarily) will activate it.
                 Many extensions may be specified separating them with a colon, or using this
                 option multiple times." in
    Arg.(value & opt_all (list string) [] & info ["x"; "ext"] ~docs ~docv:"EXTS" ~doc)
  in
  let print_proof =
    let doc = "Print proof for unsat results (implies proof generation)." in
    Arg.(value & opt (some string) None & info ["p"; "proof"] ~docs ~doc)
  in
  let print_model =
    let doc = Util.sprintf
        "Set the option for printing the model (if one is found) to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false model_list) in
    Arg.(value & opt model NoModel & info ["m"; "model"] ~docs ~docv:"MODEL" ~doc)
  in
  let time =
    let doc = "Stop the program after a time lapse of $(docv).
                 Accepts usual suffixes for durations : s,m,h,d.
                 Without suffix, default to a time in seconds." in
    Arg.(value & opt c_time 300. & info ["t"; "time"] ~docs ~docv:"TIME" ~doc)
  in
  let size =
    let doc = "Stop the program if it tries and use more the $(docv) memory space. " ^
              "Accepts usual suffixes for sizes : k,M,G,T. " ^
              "Without suffix, default to a size in octet." in
    Arg.(value & opt c_size 1_000_000_000. & info ["s"; "size"] ~docs ~docv:"SIZE" ~doc)
  in
  Term.(pure mk_opts $ bt $ quiet $ log $ debug $ file $ input $ output $ proof $ type_only $ exts $ print_proof $ print_model $ time $ size)

