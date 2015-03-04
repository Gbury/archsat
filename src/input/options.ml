
open Cmdliner

(* Type definitions for common options *)
type model =
  | None
  | Simple
  | Full

type copts = {
    (* Input/Output option *)
    formatter : Format.formatter;
    input_file : string;
    input_format : Io.input;
    output_format : Io.output;

    (* Proving options *)
    proof : bool;
    solve : bool;
    extensions : string list;

    (* Printing options *)
    print_proof : bool;
    print_model : model;

    (* Limits *)
    time_limit : float;
    size_limit : float;
}

let mk_opts file input output proof type_only exts p_proof p_model time size = {
    formatter = Format.std_formatter;
    input_file = file;
    input_format = input;
    output_format = output;

    proof = proof || p_proof;
    solve = not type_only;
    extensions = exts;

    print_model = p_model;
    print_proof = p_proof;

    time_limit = time;
    size_limit = size;
}

(* Argument converter for integer with multiplier suffix *)
let print_sint fmt f = Format.fprintf fmt "%f" f
let parse_sint arg =
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
    | 's' -> multiplier 1.
    | 'm' -> multiplier 60.
    | 'h' -> multiplier 3600.
    | 'd' -> multiplier 86400.
    | '0'..'9' -> `Ok (float_of_string arg)
    | _ -> `Error "bad numeric argument"
  with Failure "float_of_string" -> `Error "bad numeric argument"

let sint = parse_sint, print_sint

(* Argument converters for input/output *)
let input = Arg.enum [
  "auto", Io.Auto;
  "dimacs", Io.Dimacs;
  "tptp", Io.Tptp;
  "smtlib", Io.Smtlib;
]
let output = Arg.enum [
  "standard", Io.Standard;
  "dot", Io.Dot;
]
let model = Arg.enum [
  "none", None;
  "simple", Simple;
  "full", Full;
]

(* Argument parsing *)
let copts_sect = "COMMON OPTIONS"
let help_secs = [
 `S copts_sect; `P "Common options";
 `S "BUGS"; `P "TODO";
]

let copts_t =
  let docs = copts_sect in
  let file =
      let doc = "Input problem file." in
      Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let input =
      let doc = "Input format for the problem file." in
      Arg.(value & opt input Io.Auto & info ["i"; "input"] ~docs ~docv:"INPUT" ~doc)
  in
  let output =
      let doc = "Output format for printing results." in
      Arg.(value & opt output Io.Standard & info ["o"; "output"] ~docs ~docv:"OUTPUT" ~doc)
  in
  let proof =
      let doc = "If set, compute and check the resolution proofs for unsat results." in
      Arg.(value & flag & info ["check"] ~docs ~doc)
  in
  let type_only =
      let doc = "Only parse and type the given problem. Do not attempt to solve." in
      Arg.(value & flag & info ["type-only"] ~docs ~doc)
  in
  let exts =
      let doc = "Activate/deactivate extensions." in
      Arg.(value & opt (list string) [] & info ["x"; "ext"] ~docs ~docv:"EXTS" ~doc)
  in
  let print_proof =
      let doc = "Print proof for unsat results (implies proof generation)." in
      Arg.(value & flag & info ["p"; "proof"] ~docs ~doc)
  in
  let print_model =
      let doc = "Print model for sat results according to $(docv)." in
      Arg.(value & opt model None & info ["m"; "model"] ~docs ~docv:"MODEL" ~doc)
  in
  let time =
      let doc = "Stop the program after a time lapse of $(docv).
                 Accepts usual suffixes for durations : s,m,h,d.
                 Without suffix, default to a time in seconds." in
      Arg.(value & opt sint 300. & info ["t"; "time"] ~docs ~docv:"TIME" ~doc)
  in
  let size =
      let doc = "Stop the program if it tries and use more the $(docv) memory space. " ^
                "Accepts usual suffixes for sizes : k,M,G,T. " ^
                "Without suffix, default to a size in octet." in
      Arg.(value & opt sint 1_000_000. & info ["s"; "size"] ~docs ~docv:"SIZE" ~doc)
  in
  Term.(pure mk_opts $ file $ input $ output $ proof $ type_only $ exts $ print_proof $ print_model $ time $ size)

(*
let logspec () =
    let res = ref [] in
    Util.Section.iter (fun (name, s) ->
        if name <> "" then
            res := ("-debug." ^ name, Arg.Int (Util.Section.set_debug s),
                    "<lvl> Sets the debug verbose level for section " ^ name) :: !res
        );
    !res

let pp_string b s = Printf.bprintf b "%s" s

let argspec = Arg.align (List.sort arg_compare
    (Solver.get_options () @ logspec () @ [
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true),
    " Enable stack traces";
    "-debug", Arg.Int Util.set_debug,
    "<lvl> Sets the global debug verbose level";
    "-gc", Arg.Unit setup_gc_stat,
    " Outputs statistics about the GC";
    "-ext", Arg.String Dispatcher.set_exts,
    "<extensions> Activate/deactivate extensions (default : +eq,+uf,+tab,+prop,+skolem,+meta)";
  ]))

*)



