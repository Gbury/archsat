
(* Output functions *)
(* ************************************************************************ *)

let printf format =
  Format.fprintf Format.std_formatter format

(* Logging functions *)
(* ************************************************************************ *)

let debug = ref false
let need_cleanup = ref false

let enable_debug () = debug := true
let cleanup () = need_cleanup := true

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

let pp_aux ~section ~lvl format =
  if !need_cleanup then
    Format.fprintf Format.std_formatter "\r";
  let now = Time.get_total_time () in
  Format.fprintf Format.std_formatter
    ("%% [%.3f %s] @[<hov>" ^^ format ^^ "@]@.")
    now (Section.full_name section)

let aux ?(section=Section.root) lvl format =
  if lvl <= Section.cur_level section then
    if !debug then
      Logs.log ~section ~lvl format
    else
      pp_aux ~section ~lvl format
  else
    Format.ifprintf Format.std_formatter format

let error ?section = aux ?section Level.error
let log ?section = aux ?section Level.log
let warn ?section = aux ?section Level.warn
let info ?section = aux ?section Level.info
let debug ?section = aux ?section Level.debug

(* Profiling *)
(* ************************************************************************ *)

let enter_prof = Section.enter
let exit_prof = Section.exit

(* Debug output functions *)
(* ************************************************************************ *)

let rec exit_profs () =
  match Section.curr () with
  | None -> ()
  | Some section ->
    info ~section "Closing section forcefully";
    Section.exit section;
    exit_profs ()

let clean_exit () =
  exit_profs ()


