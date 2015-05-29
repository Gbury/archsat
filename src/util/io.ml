
let log_section = Util.Section.make "IO"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

exception Parsing_error of ParseLocation.t * string

(* IO settings *)
(* ************************************************************************ *)

open Options

let input = ref Auto
let output = ref Standard

let set_input i = input := i
let set_output o = output := o

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

let print_with pre post f fmt format =
  Format.fprintf fmt "%s@[<hov> " pre;
  Format.kfprintf (fun fmt -> Format.fprintf fmt "@] %s" post; f fmt) fmt format

let flush fmt = Format.fprintf fmt "@."

let fprintf fmt format =
  let res = match !output with
    | Standard -> Format.kfprintf flush fmt format
    | Dot -> print_with "/*" "*/" flush fmt format
  in
  res

let print_model fmt l =
  let aux (t, v) = fprintf fmt "%a -> %a" Expr.Print.term t Expr.Print.term v in
  List.iter aux l

let print_proof fmt p =
  match !output with
  | Standard -> fprintf fmt "Standard proof output not supported yet."
  | Dot -> Solver.print_proof_dot fmt p

let print_res fmt status =
  fprintf fmt "%s (%.3f)" status (Sys.time ())


