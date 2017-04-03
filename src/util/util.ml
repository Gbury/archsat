
(* Mutable state *)
(* ************************************************************************ *)

let debug = ref false
let need_cleanup = ref false

let enable_debug () = debug := true
let cleanup () = need_cleanup := true

(* Output functions *)
(* ************************************************************************ *)

let printf format =
  if !debug then
    Logs.log ~section:Section.root ~lvl:Level.log format
  else
    CCFormat.with_colorf "reset" Format.std_formatter format

(* Logging functions *)
(* ************************************************************************ *)

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

let pp_time ~lvl fmt section =
  if not (Level.equal Level.error lvl) then
    Format.fprintf fmt "%% [%.3f %s] "
      (Time.get_total_time ()) (Section.full_name section)

let pp_aux ~section ~lvl format =
  if !need_cleanup then
    Format.fprintf Format.std_formatter "\r";
  CCFormat.with_colorf
    (Level.color lvl) Format.std_formatter
    ("%a%a@[<hov>" ^^ format ^^ "@]@.")
    (pp_time ~lvl) section Level.prefix lvl

let aux ?(section=Section.root) lvl format =
  let cur_lvl = Section.cur_level section in
  if Level.compare lvl cur_lvl <= 0 then
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


