
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
      List.rev_map (List.rev_map Sat.mk_prop) (Parsedimacs.parse file)
    with Parsedimacs.Syntax_error l ->
      raise (Syntax_error (l, 0, "Dimacs parsing error"))

let parse_input file =
  parse_with_input file (match !input with
      | Auto -> format_of_filename file
      | f -> f)

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

