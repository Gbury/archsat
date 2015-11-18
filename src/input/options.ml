
let misc_section = Util.Section.make "misc"

let section = Util.Section.make ~parent:misc_section "options"
let log i fmt = Util.debug ~section i fmt

open Cmdliner

(* Type definitions for common options *)
(* ************************************************************************ *)

type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

type output =
  | Standard
  | SZS

type profile_options = {
  enabled : bool;
  max_depth : int option;
  sections : Util.Section.t list;
  raw_data : Format.formatter;
  print_stats : bool;
}

type copts = {
  (* Input/Output option *)
  out : Format.formatter;
  input_file : string;
  input_format : input;
  output_format : output;
  interactive : bool;

  (* Proving options *)
  solve : bool;
  proof : bool;
  addons : string list;
  plugins : string list;

  (* Printing options *)
  dot_proof : Format.formatter;
  model_out : Format.formatter;

  (* Time/Memory options *)
  profile : profile_options;
  time_limit : float;
  size_limit : float;
}

(* Misc *)
(* ************************************************************************ *)

let formatter_of_descr = function
  | "" -> Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
  | "stdout" -> Format.std_formatter
  | s -> Format.formatter_of_out_channel (open_out s)

(* Option values *)
(* ************************************************************************ *)

let mk_opts () file input output interactive proof type_only plugins addons
    dot_proof model_out time size profile =
  {
    out = Format.std_formatter;
    input_file = file;
    input_format = input;
    output_format = output;
    interactive = interactive || file = "stdin";

    solve = not type_only;
    proof = proof || dot_proof <> "";
    addons = List.concat addons;
    plugins = List.concat plugins;

    model_out = formatter_of_descr model_out;
    dot_proof = formatter_of_descr dot_proof;

    profile = profile;
    time_limit = time;
    size_limit = size;
  }

let profile_opts enable depth l out stats = {
  enabled = enable || depth <> None || l <> [] || out <> "";
  max_depth = depth;
  sections = l;
  raw_data = formatter_of_descr out;
  print_stats = stats;
}

(* Side-effects options *)
let set_opts gc bt quiet log debug =
  if gc then
    at_exit (fun () -> Gc.print_stat stdout;);
  (* Backtrace printing *)
  if bt then
    Printexc.record_backtrace true;
  (* Set up debug levels *)
  if quiet then
    Util.Section.clear_debug Util.Section.root
  else begin
    Util.set_debug log;
    List.iter (fun (s, lvl) -> Util.Section.set_debug s lvl) debug
  end

let clean opt = ()

(* Argument converter for integer with multiplier suffix *)
(* ************************************************************************ *)

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
  (print_aux "To" n_tera) ^
  (print_aux "Go" n_giga) ^
  (print_aux "Mo" n_mega) ^
  (print_aux "ko" n_kilo) ^
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

(* Printing function *)
(* ************************************************************************ *)

let input_string = function
  | Auto -> "auto"
  | Dimacs -> "dimacs"
  | Tptp -> "tptp"
  | Smtlib -> "smtlib"

let output_string = function
  | Standard -> "standard"
  | SZS -> "SZS"

let stringify f l = List.map (fun x -> (f x, x)) l

let input_list = stringify input_string [Auto; Dimacs; Tptp; Smtlib]
let output_list = stringify output_string [Standard; SZS]

let bool_opt s bool = if bool then Printf.sprintf "[%s]" s else ""

let log_opts opt =
  log 0 "Limits : %s / %s" (time_string opt.time_limit) (size_string opt.size_limit);
  log 0 "Options : %s%s%s[in: %s][out: %s]"
    (bool_opt "profile" opt.profile.enabled) (bool_opt "solve" opt.solve) (bool_opt "check_proof" opt.proof)
    (input_string opt.input_format) (output_string opt.output_format);
  log 0 "Input file : %s" opt.input_file

(* Other Argument converters *)
(* ************************************************************************ *)

(* Input/Output formats *)
let input = Arg.enum input_list
let output = Arg.enum output_list

(* Converter for sections *)
let print_section fmt s = Format.fprintf fmt "%s" (Util.Section.full_name s)
let parse_section arg =
  try `Ok (Util.Section.find arg)
  with Not_found -> `Error ("Invalid debug section '" ^ arg ^ "'")

let section = parse_section, print_section

(* Converter for output file descriptor (with stdout as special case) *)
let print_descr fmt = function
  | "" -> Format.fprintf fmt "<none>"
  | s -> Format.fprintf fmt "%s" s

let parse_descr = function
  | "stdout" -> `Ok "stdout"
  | f ->
    if Sys.is_directory f then
      `Error (Format.sprintf "File %s is a directory" f)
    else
      `Ok f

let out_descr = parse_descr, print_descr

(* Argument parsing *)
(* ************************************************************************ *)

let copts_sect = "COMMON OPTIONS"
let prof_sect = "PROFILING OPTIONS"
let ext_sect = "ADVANCED OPTIONS"
let help_secs ext_doc sext_doc = [
  `S copts_sect; `P "Common options for the prover";
  `S "ADDONS"; `P "Addons are typing/semantic extensions that extend typing
  to include builtins of languages.";
] @ sext_doc @ [
    `S "PLUGINS"; `P "Available extensions are listed in this section. Each paragraph starts with the extension's priority
      and name, and then a short description of what the extension does. Extensions with higher priorities
      are called earlier than those with lower priorities.";
  ] @ ext_doc @ [
    `S ext_sect; `P "Options primarily used by the extensions (use only if you know what you're doing !).";
    `S prof_sect;
    `S "BUGS"; `P "TODO";
  ]

let log_sections () =
  let l = ref [] in
  Util.Section.iter (fun (name, _) -> if name <> "" then l := name :: !l);
  List.sort Pervasives.compare !l

let profile_t =
  let docs = prof_sect in
  let profile =
    let doc = "Activate time profiling of the prover." in
    Arg.(value & flag & info ["p"; "profile"] ~docs ~doc)
  in
  let depth =
    let doc = "Maximum depth for profiling" in
    Arg.(value & opt (some int) None & info ["pdepth"] ~doc ~docs)
  in
  let sects =
    let doc = "Section to be profiled with its children (overrides pdeth setting locally)" in
    Arg.(value & opt_all section [] & info ["psection"] ~doc ~docs)
  in
  let raw_data =
    let doc = "Set a file to which output the raw profiling data.
               A special 'stdout' value can be used to use standard output." in
    Arg.(value & opt out_descr "" & info ["pdata"] ~docs ~doc)
  in
  let stats =
    let doc = "Print statistics" in
    Arg.(value & flag & info ["stats"] ~docs ~doc)
  in
  Term.(pure profile_opts $ profile $ depth $ sects $ raw_data $ stats)

let copts_t () =
  let docs = copts_sect in
  let gc =
    let doc = "Print statistics about the gc upon exiting" in
    Arg.(value & flag & info ["g"; "gc"] ~docs:ext_sect ~doc)
  in
  let bt =
    let doc = "Enables printing of backtraces." in
    Arg.(value & flag & info ["b"; "backtrace"] ~docs:ext_sect ~doc)
  in
  let quiet =
    let doc = "Supress all output but the result status of the problem" in
    Arg.(value & flag & info ["q"; "quiet"] ~docs ~doc)
  in
  let interactive =
    let doc = "Use archsat in interactive mode (equivalent to using 'stdin' as input file)" in
    Arg.(value & flag & info ["interactive"] ~docs ~doc)
  in
  let log =
    let doc = "Set the global level for debug outpout." in
    Arg.(value & opt int 0 & info ["v"; "verbose"] ~docs ~docv:"LVL" ~doc)
  in
  let debug =
    let doc = CCPrint.sprintf
        "Set the debug level of the given section, as a pair : '$(b,section),$(b,level)'.
        $(b,section) might be %s." (Arg.doc_alts ~quoted:false (log_sections ())) in
    Arg.(value & opt_all (pair section int) [] & info ["debug"] ~docs:ext_sect ~docv:"NAME,LVL" ~doc)
  in
  let file =
    let doc = "Input problem file, 'stdin' can be used for interactive mode" in
    Arg.(value & pos 0 non_dir_file "stdin" & info [] ~docv:"FILE" ~doc)
  in
  let input =
    let doc = CCPrint.sprintf
        "Set the format for the input file to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false input_list) in
    Arg.(value & opt input Auto & info ["i"; "input"] ~docs ~docv:"INPUT" ~doc)
  in
  let output =
    let doc = CCPrint.sprintf
        "Set the output for printing results to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false  output_list) in
    Arg.(value & opt output Standard & info ["o"; "output"] ~docs ~docv:"OUTPUT" ~doc)
  in
  let check_proof =
    let doc = "If set, compute and check the resolution proofs for unsat results. This option
               does not trigger printing of the proof, for that a proof format printing option
               (such as the $(b,--dot) option) must be used." in
    Arg.(value & flag & info ["c"; "check"] ~docs ~doc)
  in
  let type_only =
    let doc = "Only parse and type the given problem. Do not attempt to solve." in
    Arg.(value & flag & info ["type-only"] ~docs ~doc)
  in
  let plugins =
    let doc = "Activate/deactivate extensions, using their names (see EXTENSIONS section).
                 Prefixing an extension with a $(b,'-') deactivates it, while using only its name
                 (possibly with the $(b,'+') prefix, but not necessarily) will activate it.
                 Many extensions may be specified separating them with a colon, or using this
                 option multiple times." in
    Arg.(value & opt_all (list string) [] & info ["x"; "ext"] ~docs ~docv:"EXTS" ~doc)
  in
  let addons =
    let doc = "Activate/deactivate syntax extensions. See the extension options
               for more documentation." in
    Arg.(value & opt_all (list string) [] & info ["semantics"] ~docs ~doc)
  in
  let dot_proof =
    let doc = "Set the file to which the program sould output a proof in dot format.
               A special 'stdout' value can be used to use standard output." in
    Arg.(value & opt out_descr "" & info ["dot"] ~docs ~doc)
  in
  let model_out =
    let doc = CCPrint.sprintf
        "Set the file to which output a model (if found). A special value
        'stdout' can be used to output on standard output." in
    Arg.(value & opt out_descr "" & info ["m"; "model"] ~docs ~docv:"MODEL" ~doc)
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
  Term.(pure mk_opts $ (pure set_opts $ gc $ bt $ quiet $ log $ debug) $
        file $ input $ output $ interactive $ check_proof $ type_only $ plugins $ addons $ dot_proof $ model_out $ time $ size $ profile_t)

