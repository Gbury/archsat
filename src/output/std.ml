
(* Some helper functions *)
(* ************************************************************************ *)

let start = ref 0.

let set_start () = start := Util.get_total_time ()

let flush fmt () =
  Format.fprintf fmt "@."

(* Output functions *)
(* ************************************************************************ *)

let print_status opt fmt status =
  Format.fprintf fmt "%s (%.3f)@." status (Util.get_total_time () -. !start)

let print_sat opt fmt = print_status opt fmt "Sat"
let print_unsat opt fmt = print_status opt fmt "Unsat"
let print_unknown opt fmt = print_status opt fmt "Unknown"

let print_error opt fmt = function
  | Options.Sigint ->
    Format.fprintf fmt "User interrupt@."
  | Options.Out_of_time ->
    print_status opt fmt "Timeout"
  | Options.Out_of_space ->
    print_status opt fmt "Out of space"
  | exn ->
    Format.fprintf fmt "%a@\n%s@."
      (print_status opt) "Uncaught exception" (Printexc.to_string exn)
