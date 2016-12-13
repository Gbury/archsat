
(* Misc functions *)
(* ************************************************************************ *)

let prelude _ = ""

(* Output functions *)
(* ************************************************************************ *)

let flush fmt () =
  Format.fprintf fmt "@."

let print_res opt fmt status =
  Format.fprintf fmt "%% SZS status %s for %s"
    status (Options.input_to_string opt.Options.input_file)

let print_status opt fmt status =
  Format.fprintf fmt "%a@." (print_res opt) status

let print_sat opt fmt = print_status opt fmt "CounterSatisfiable"
let print_unsat opt fmt = print_status opt fmt "Theorem"
let print_unknown opt fmt = print_status opt fmt "Unknown"
let print_timeout opt fmt = print_status opt fmt "TimeOut"
let print_spaceout opt fmt = print_status opt fmt "MemoryOut"

let print_exn opt fmt exn =
  Format.fprintf fmt "%a@." (print_res opt) "Error"

