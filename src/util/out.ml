
let section = Util.Section.make ~parent:Options.misc_section "IO"
let log i fmt = Util.debug ~section i fmt

(* IO settings *)
(* ************************************************************************ *)

open Options

let output = ref Standard
let input_file = ref ""
let curr_output () = !output

let set_output o = output := o
let set_input_file f = input_file := f

(* Output functions *)
(* ************************************************************************ *)

let start = ref 0.

let set_start () = start := Util.get_total_time ()

let flush fmt = Format.fprintf fmt "@."

let print_szs_status fmt status =
  Format.fprintf fmt "%% SZS status %s for %s" status !input_file

let print_res fmt status =
  Format.fprintf fmt "%s (%.3f)" status (Util.get_total_time () -. !start)

let print_sat fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Sat"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "CounterSatisfiable"

let print_unsat fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Unsat"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "Theorem"

let print_unknown fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Unknown"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "Unknown"

let print_error fmt format = match !output with
  | Standard ->
    Format.fprintf fmt "%a@\n" print_res "Error";
    Format.kfprintf flush fmt format
  | SZS ->
    Format.fprintf fmt "%a : " print_szs_status "Error";
    Format.kfprintf flush fmt format

let print_timeout fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Timeout"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "Timeout"

let print_spaceout fmt = match !output with
  | Standard -> Format.fprintf fmt "%a@." print_res "Out of Memory"
  | SZS -> Format.fprintf fmt "%a@." print_szs_status "MemoryOut"

