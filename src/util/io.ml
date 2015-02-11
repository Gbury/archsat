
(* Type definitions *)
(* ************************************************************************ *)

exception Parsing_error of ParseLocation.t * string
exception Setting_not_found of string * string * string list

type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

type output =
  | Standard
  | Dot

(* IO settings *)
(* ************************************************************************ *)

let input = ref Auto
let output = ref Standard

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

let set_flag opt arg flag l =
  try flag := List.assoc arg l
  with Not_found -> raise (Setting_not_found (opt, arg, List.map fst l))

let set_input s = set_flag "Input" s input input_list
let set_output s = set_flag "Output" s output output_list

let accepted_input = List.map fst input_list
let accepted_output = List.map fst output_list

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
  | Auto -> input := format_of_filename file; parse_input file
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
  let aux (t, v) = fprintf fmt "%a -> %a" Expr.print_term t Expr.print_term v in
  List.iter aux l

let print_proof fmt p =
  match !output with
  | Standard -> fprintf fmt "Standard proof output not supported yet."
  | Dot -> Solver.print_proof_dot fmt p

let print_res fmt status time =
  fprintf fmt "%s (%.3f)"  status time


