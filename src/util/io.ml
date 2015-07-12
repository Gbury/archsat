
let log_section = Util.Section.make ~parent:Options.misc_section "IO"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

exception Parsing_error of ParseLocation.t * string

(* IO settings *)
(* ************************************************************************ *)

open Options

let input = ref Auto
let output = ref Standard
let input_file = ref ""

let set_input i = input := i
let set_output o = output := o
let set_input_file f = input_file := f

let pp_input b = function
  | Auto -> Printf.bprintf b "auto"
  | Dimacs -> Printf.bprintf b "dimacs"
  | Tptp -> Printf.bprintf b "tptp"
  | Smtlib -> Printf.bprintf b "smtlib"

(* Input functions *)
(* ************************************************************************ *)

let format_of_filename s =
  let last n =
    try String.sub s (String.length s - n) n
    with Invalid_argument _ -> ""
  in
  if last 2 = ".p" then
    Tptp
  else if last 4 = ".cnf" then
    Dimacs
  else if last 5 = ".smt2" then
    Smtlib
  else (* Default choice *)
    Dimacs

let rec parse_input file = match !input with
  | Auto ->
    input := format_of_filename file;
    log 1 "Detected input format : %a" pp_input !input;
    parse_input file
  | Dimacs ->
    begin try
        Dimacs.parse_file file
      with Dimacs.Parse_error l ->
        raise (Parsing_error (ParseLocation.mk file l 0 l 0, "Dimacs parsing error"))
    end
  | Tptp ->
    begin try
        Tptp.parse_file ~recursive:true file
      with Tptp.Parse_error (loc, msg) ->
        raise (Parsing_error (loc, msg))
    end
  | Smtlib -> Smtlib.parse_file file

let input_env () = Semantics.type_env !input

(* Output functions *)
(* ************************************************************************ *)

let flush fmt = Format.fprintf fmt "@."

let print_model _ _ = ()

let print_proof _ _ _ = ()

let print_szs_status fmt status =
  Format.fprintf fmt "%% SZS status %s for %s" status !input_file

let print_res fmt status =
  Format.fprintf fmt "%s (%.3f)" status (Sys.time ())

let print_sat fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Sat"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "CounterSatisfiable"

let print_unsat fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Unsat"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "Theorem"

let print_error fmt format = match !output with
  | Standard ->
    Format.fprintf fmt "%a@\n" print_res "Error";
    Format.kfprintf flush fmt format
  | SZS ->
    Format.fprintf fmt "%a : " print_res "Error";
    Format.kfprintf flush fmt format

let print_timeout fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Timeout"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "Timeout"

let print_spaceout fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Outof Memory"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "MemoryOut"

