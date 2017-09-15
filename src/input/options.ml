
let misc_section = Section.make "misc"
open Cmdliner

(* Exceptions *)
(* ************************************************************************ *)

exception Sigint
exception Out_of_time
exception Out_of_space
exception File_not_found of string
exception Stmt_not_implemented of Dolmen.Statement.t

(* Type definitions for common options *)
(* ************************************************************************ *)

type input = In.language

type output =
  | Standard
  | SZS

type mode =
  | Debug
  | Regular
  | Interactive

type status =
  | Ok
  | Errored

type input_options = {
  mode    : mode;
  format  : input option;
  dir     : string;
  file    : [ `Stdin | `File of string];
}

type output_options = {
  format  : output;
  icnf    : Format.formatter option;
  dimacs  : Format.formatter option;
}

type typing_options = {
  infer   : bool;
  explain : [ `No | `Yes | `Full ];
}

type profile_options = {
  enabled       : bool;
  max_depth     : int option;
  sections      : Section.t list;
  raw_data      : Format.formatter option;
}

type stats_options = {
  enabled       : bool;
}

type proof_options = {
  active      : bool;
  context     : bool;
  dot         : Format.formatter option;
  unsat_core  : Format.formatter option;
  coq         : Format.formatter option;
}

type model_options = {
  active      : bool;
  assign      : Format.formatter option;
}

type opts = {

  (* Internal status *)
  status  : status;

  (* Input&output options *)
  input   : input_options;
  output  : output_options;

  (* Typing options *)
  typing  : typing_options;

  (* Proof&model options *)
  proof   : proof_options;
  model   : model_options;

  (* Solving options *)
  solve   : bool;
  addons  : string list;
  plugins : string list;

  (* Time/Memory options *)
  time_limit  : float;
  size_limit  : float;
  profile     : profile_options;
  stats       : stats_options;
}

(* Manipulate options *)
(* ************************************************************************ *)

let error opt =
  if opt.input.mode = Interactive then opt
  else { opt with status = Errored }

(* Misc *)
(* ************************************************************************ *)

let input_to_string = function
  | `Stdin -> "<stdin>"
  | `File f -> f

let formatter_of_out_descr = function
  | `None -> None
  | `Stdout -> Some (Format.std_formatter)
  | `File s -> Some (Format.formatter_of_out_channel (open_out s))

(* Option values *)
(* ************************************************************************ *)

let input_opts fd format debug =
  let dir, file =
    match fd with
    | `Stdin ->
      Sys.getcwd (), `Stdin
    | `File f ->
      Filename.dirname f, `File (Filename.basename f)
  in
  match fd, debug with
  | `File _, true ->
    `Ok { mode = Debug; format; dir; file; }
  | `File _, false ->
    `Ok { mode = Regular; format; dir; file; }
  | `Stdin, false ->
    `Ok { mode = Interactive; format; dir; file; }
  | `Stdin, true ->
    `Error (false, "Cannot read stdin and use debug mode")

let output_opts format export_dimacs export_icnf =
  let dimacs = formatter_of_out_descr export_dimacs in
  let icnf = formatter_of_out_descr export_icnf in
  { format; dimacs; icnf; }

let typing_opts infer explain =
  { infer; explain; }

let profile_opts enable max_depth sections out =
  let enabled =
    enable
    || max_depth <> None
    || sections <> []
    || out <> `None
  in
  { enabled; max_depth; sections;
    raw_data = formatter_of_out_descr out; }

let stats_opts enabled =
  { enabled; }

let proof_opts prove no_context dot unsat_core coq =
  let context = not no_context in
  let dot = formatter_of_out_descr dot in
  let unsat_core = formatter_of_out_descr unsat_core in
  let coq = formatter_of_out_descr coq in
  let active = prove
               || dot <> None
               || unsat_core <> None
               || coq <> None
  in
  { active; context; dot; unsat_core; coq; }

let model_opts active assign = {
  active;
  assign = formatter_of_out_descr assign;
}

(* Side-effects options *)
let set_opts gc bt quiet lvl log_time debug msat_log colors opt =
  CCFormat.set_color_default colors;
  if gc then at_exit (fun () -> Gc.print_stat stdout;);
  if bt then Printexc.record_backtrace true;
  if quiet then Section.clear_debug Section.root
  else begin
    let () =
      match formatter_of_out_descr msat_log with
      | None -> ()
      | Some fmt ->
        Msat.Log.set_debug 9999;
        Msat.Log.set_debug_out fmt
    in
    let level =
      if (opt.input.mode = Interactive)
      then Level.(max log lvl) else lvl
    in
    if not log_time then Util.disable_time ();
    Section.set_debug Section.root level;
    List.iter (fun (s, lvl) -> Section.set_debug s lvl) debug
  end;
  opt

let mk_opts
    input output typing
    proof model
    profile stats
    type_only
    plugins addons
    time size
  =
  {
    status = Ok;

    input;
    output;
    typing;
    proof;
    model;

    solve = not type_only;
    addons = List.concat addons;
    plugins = List.concat plugins;

    profile; stats;
    time_limit = time;
    size_limit = size;
  }

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
  with Failure _ -> `Error "bad numeric argument"

let print_size = Util.print_size

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
  with Failure _ -> `Error "bad numeric argument"

let c_time = parse_time, print_time
let c_size = parse_size, print_size

(* Printing function *)
(* ************************************************************************ *)

let output_string = function
  | Standard -> "standard"
  | SZS -> "SZS"

let stringify f l = List.map (fun x -> (f x, x)) l

let output_list = stringify output_string [Standard; SZS]

let output_mode = function
  | Regular -> ""
  | Debug -> "[debug]"
  | Interactive -> "[interactive]"

let bool_opt s bool = if bool then Printf.sprintf "[%s]" s else ""

let log_opts opt =
  Util.log "Limits : %s / %a"
    (time_string opt.time_limit) print_size opt.size_limit;
  Util.log "Options : %s%s%s%s[in: %s][out: %s]"
    (output_mode opt.input.mode)
    (bool_opt "solve" opt.solve)
    (bool_opt "prove" opt.proof.active)
    (bool_opt "profile" opt.profile.enabled)
    (CCOpt.get_or ~default:"auto" @@
     CCOpt.map In.string_of_language @@ opt.input.format)
    (output_string opt.output.format);
  Util.log "Input dir : '%s'" opt.input.dir;
  Util.log "Input file : %s" (input_to_string opt.input.file)

(* Other Argument converters *)
(* ************************************************************************ *)

(* Input/Output formats *)
let input = Arg.enum In.enum
let output = Arg.enum output_list

(* Converter for input file/stdin *)
let in_fd =
  let parse x = `Ok (`File x) in
  let print fmt i = Format.fprintf fmt "%s" (input_to_string i) in
  parse, print

(* Converter for sections *)
let print_section fmt s =
  Format.fprintf fmt "%s" (Section.full_name s)

let parse_section arg =
  try `Ok (Section.find arg)
  with Not_found -> `Error ("Invalid debug section '" ^ arg ^ "'")

let section = parse_section, print_section

(* Converter for logging level *)
let level_list = [
  "log",    Level.log;
  "error",  Level.error;
  "warn",   Level.warn;
  "info",   Level.info;
  "debug",  Level.debug;
]

let level = Arg.enum level_list

(* Converter for explain option *)
let explain_list = [
  "no",   `No;
  "yes",  `Yes;
  "full", `Full;
]

let explain = Arg.enum explain_list

(* Converter for output file descriptor (with stdout as special case) *)
let print_descr fmt = function
  | `None -> Format.fprintf fmt "<none>"
  | `Stdout -> Format.fprintf fmt "<stdout>"
  | `File s -> Format.fprintf fmt "%s" s

let parse_descr = function
  | "stdout" -> `Ok `Stdout
  | f ->
    try
      if Sys.file_exists f && Sys.is_directory f then
          `Error (Format.sprintf "File '%s' is a directory" f)
      else
        `Ok (`File f)
    with Sys_error _ ->
      `Error (Format.sprintf
                "system error while asserting wether '%s' is an existing file or directory" f)

let out_descr = parse_descr, print_descr

(* Argument parsing *)
(* ************************************************************************ *)

let copts_sect = "COMMON OPTIONS"
let prof_sect = "PROFILING OPTIONS"
let stats_sect = "STATISTICS OPTIONS"
let ext_sect = "ADVANCED OPTIONS"
let proof_sect = "PROOF OPTIONS"
let model_sect = "MODEL OPTIONS"

let help_secs ext_doc sext_doc = [
  `S copts_sect;
  `P "Common options for the prover";
  `S "ADDONS";
  `P "Addons are typing/semantic extensions that extend typing to include builtins of languages.";
] @ sext_doc @ [
    `S "PLUGINS"; `P "Available extensions are listed in this section. Each paragraph starts with the extension's priority
      and name, and then a short description of what the extension does. Extensions with higher priorities
      are called earlier than those with lower priorities.";
  ] @ ext_doc @ [
    `S proof_sect;
    `S model_sect;
    `S ext_sect;
    `P "Options primarily used by the extensions (use only if you know what you're doing !).";
    `S prof_sect;
    `S stats_sect;
    `S "BUGS";
    `P "TODO";
  ]

let log_sections () =
  let l = ref [] in
  Section.iter (fun s ->
      if not Section.(equal root s) then l := Section.full_name s :: !l);
  List.sort Pervasives.compare !l

let input_t =
  let docs = copts_sect in
  let fd =
    let doc = "Input problem file. If no file is specified,
               archsat will enter interactive mode and read on stdin." in
    Arg.(value & pos 0 in_fd `Stdin & info [] ~docv:"FILE" ~doc)
  in
  let format =
    let doc = Format.asprintf
        "Set the format for the input file to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false In.enum) in
    Arg.(value & opt (some input) None & info ["i"; "input"] ~docs ~docv:"INPUT" ~doc)
  in
  let debug =
    let doc = "Start in debug mode" in
    Arg.(value & flag & info ["debug"] ~docs ~doc)
  in
  Term.(ret (const input_opts $ fd $ format $ debug))

let output_t =
  let docs = copts_sect in
  let format =
    let doc = Format.asprintf
        "Set the output format to $(docv) (%s)."
        (Arg.doc_alts_enum ~quoted:false output_list) in
    Arg.(value & opt output Standard & info ["o"; "output"] ~docs ~docv:"OUTPUT" ~doc)
  in
  let export_dimacs =
    let doc = "Export the full SAT problem to dimacs format in the given file" in
    Arg.(value & opt out_descr `None & info ["export-dimacs"] ~docs ~doc)
  in
  let export_icnf =
    let doc = "Export the full SAT problem to icnf format in the given file" in
    Arg.(value & opt out_descr `None & info ["export-icnf"] ~docs ~doc)
  in
  Term.(const output_opts $ format $ export_dimacs $ export_icnf)

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
    Arg.(value & opt out_descr `None & info ["pdata"] ~docs ~doc)
  in
  Term.(const profile_opts $ profile $ depth $ sects $ raw_data)

let stats_t =
  let docs = stats_sect in
  let enabled =
    let doc = "Print statistics" in
    Arg.(value & flag & info ["stats"] ~docs ~doc)
  in
  Term.(const stats_opts $ enabled)

let proof_t =
  let docs = proof_sect in
  let check_proof =
    let doc = "If set, compute and check the resolution proofs for unsat results. This option
               does not trigger printing of the proof, for that a proof format printing option
               (such as the $(b,--dot) option) must be used." in
    Arg.(value & flag & info ["proof"] ~docs ~doc)
  in
  let no_context =
    let doc = "Prevent printing context before the formal proof
               (only meaningful for certifying proof outputs such as coq, dedukti, ...)" in
    Arg.(value & flag & info ["no-context"] ~docs ~doc)
  in
  let dot_proof =
    let doc = "Set the file to which the program sould output a proof in dot format.
               A special 'stdout' value can be used to use standard output." in
    Arg.(value & opt out_descr `None & info ["dot"] ~docs ~doc)
  in
  let unsat_core =
    let doc = "Set the file to which the program sould output the unsat core, i.e the list
               of hypothesis used in the proof.
               A special 'stdout' value can be used to use standard output." in
    Arg.(value & opt out_descr `None & info ["unsat-core"] ~docs ~doc)
  in
  let coq =
    let doc = "Set the file to which the program should output a coq proof.
               A special 'stdout' value can be used to use standard output" in
    Arg.(value & opt out_descr `None & info ["coq"] ~docs ~doc)
  in
  Term.(const proof_opts $ check_proof $ no_context $ dot_proof $ unsat_core $ coq)

let model_t =
  let docs = model_sect in
  let active =
    let doc = "If set, compute and check the first-order models found. This option
               does not trigger printing of the model, for that use the other options." in
    Arg.(value & flag & info ["m"; "model"] ~docs ~doc)
  in
  let assign =
    let doc = "TODO" in
    Arg.(value & opt out_descr `None & info ["assign"] ~docs ~doc)
  in
  Term.(const model_opts $ active $ assign)

let unit_t =
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
  let log =
    let doc = "Set the global level for debug outpout." in
    Arg.(value & opt level Level.log & info ["v"; "verbose"] ~docs ~docv:"LVL" ~doc)
  in
  let log_time =
    let doc = "Enable time printing in the log output" in
    Arg.(value & opt bool true & info ["log-time"] ~docs ~doc)
  in
  let debug =
    let doc = Format.asprintf
        "Set the debug level of the given section, as a pair : '$(b,section),$(b,level)'.
        $(b,section) might be %s." (Arg.doc_alts ~quoted:false (log_sections ())) in
    Arg.(value & opt_all (pair section level) [] & info ["log"] ~docs:ext_sect ~docv:"NAME,LVL" ~doc)
  in
  let msat_log =
    let doc = "File to output full msat log into" in
    Arg.(value & opt out_descr `None & info ["msat"] ~docs ~doc)
  in
  let colors =
    let doc = "Activate coloring of output" in
    Arg.(value & opt bool true & info ["color"] ~docs ~doc)
  in
  Term.(const set_opts $ gc $ bt $ quiet $ log $ log_time $ debug $ msat_log $ colors)

let type_t =
  let docs = copts_sect in
  let infer =
    let doc = Format.asprintf
        "Force inference of non-declared symbols according to context" in
    Arg.(value & flag & info ["infer"] ~docs ~doc)
  in
  let explain =
    let doc = Format.asprintf
        "Explain more precisely typing conflicts, $(docv) may be %s"
        (Arg.doc_alts_enum ~quoted:false explain_list) in
    Arg.(value & opt explain `No & info ["type-explain"] ~docs ~docv:"EXPL" ~doc)
  in
  Term.(const typing_opts $ infer $ explain)

let copts_t () =
  let docs = copts_sect in
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
  Term.(unit_t $ (
      const mk_opts
      $ input_t $ output_t $ type_t
      $ proof_t $ model_t
      $ profile_t $ stats_t
      $ type_only $ plugins $ addons $ time $ size)
    )



