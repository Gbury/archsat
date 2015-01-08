
(* Type definitions *)
(* ************************************************************************ *)
exception Syntax_error of int * int * string

type input =
  | Auto
  | Dimacs

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
]

let output_list = [
  "dot", Dot;
]

let error_msg opt arg l =
  Format.fprintf Format.str_formatter "'%s' is not a valid argument for '%s', valid arguments are : %a"
    arg opt (fun fmt -> List.iter (fun (s, _) -> Format.fprintf fmt "%s, " s)) l;
  Format.flush_str_formatter ()

let set_flag opt arg flag l =
  try
    flag := List.assoc arg l
  with Not_found ->
    invalid_arg (error_msg opt arg l)

let set_input s = set_flag "Input" s input input_list
let set_output s = set_flag "Output" s output output_list

(* Input functions *)
(* ************************************************************************ *)

let format_of_filename s =
  let last n =
    try String.sub s (String.length s - n) n
    with Invalid_argument _ -> ""
  in
  if last 4 = ".cnf" then
    Dimacs
    (*
  else if last 5 = ".smt2" then
    Smtlib
    *)
  else (* Default choice *)
    Dimacs

let parse_with_input file = function
  | Auto -> assert false
  | Dimacs ->
    try
      List.rev_map (List.rev_map Bool.mk_prop) (Parsedimacs.parse file)
    with Parsedimacs.Syntax_error l ->
      raise (Syntax_error (l, 0, "Dimacs parsing error"))

let parse_input file =
  parse_with_input file (match !input with
      | Auto -> format_of_filename file
      | f -> f)

(* Output functions *)
(* ************************************************************************ *)

let print_with pre post fmt format =
    Format.fprintf fmt "%s@[<hov>" pre;
    let res = Format.fprintf fmt format in
    Format.fprintf fmt "@]%s" post;
    res

let fprintf fmt format = match !output with
    | Standard -> Format.fprintf fmt format
    | Dot -> print_with "/*" "*/" fmt format





