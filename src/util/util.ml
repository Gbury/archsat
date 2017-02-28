
(* Output functions *)
(* ************************************************************************ *)

let printf format =
  Format.fprintf Format.std_formatter format

(* Logging functions *)
(* ************************************************************************ *)

let need_cleanup = ref false
let cleanup () = need_cleanup := true

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

let aux ?(section=Section.root) l format =
  let fmt = Format.std_formatter in
  if l <= Section.cur_level section
  then begin
    if !need_cleanup then Format.fprintf fmt "\r";
    let now = Time.get_total_time () in
    Format.fprintf fmt ("%% [%.3f %s] @[<hov>" ^^ format ^^ "@]@.")
      now (Section.full_name section)
  end else
    Format.ifprintf fmt format

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


