
(* Mutable state *)
(* ************************************************************************ *)

let debug = ref false
let need_cleanup = ref false

let enable_debug () = debug := true
let cleanup () = need_cleanup := true

let time = ref true
let disable_time () = time := false

(* Siez computation *)
(* ************************************************************************ *)

let size x =
  let t = Obj.repr x in
  let h = Obj.reachable_words t in
  (float) h *. (float) Sys.word_size /. 8.

let size_string f =
  let n = int_of_float f in
  let aux n div = n / div, n mod div in
  let n_tera, n = aux n 1_000_000_000_000 in
  let n_giga, n = aux n 1_000_000_000 in
  let n_mega, n = aux n 1_000_000 in
  let n_kilo, n = aux n 1_000 in
  let print_aux s n = if n <> 0 then (string_of_int n) ^ s else "" in
  (print_aux "To" n_tera) ^
  (print_aux "Go" n_giga) ^
  (print_aux "Mo" n_mega) ^
  (print_aux "ko" n_kilo) ^
  (print_aux "" n)

let print_size fmt f =
  Format.fprintf fmt "%s" (size_string f)

(* Output functions *)
(* ************************************************************************ *)

let printf format =
  CCFormat.with_colorf "reset" Format.std_formatter (format ^^ "@.")

(* Logging functions *)
(* ************************************************************************ *)

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

let pp_time ~lvl fmt section =
  if not (Level.equal Level.error lvl) then begin
    if !time then
      Format.fprintf fmt "@{<Black>%% [%.3f %s]@} "
        (Time.get_total_time ()) (Section.full_name section)
    else
      Format.fprintf fmt "@{<Black>%% [%s]@} " (Section.full_name section)
  end

let pp_aux ~section ~lvl format =
  if !need_cleanup then
    Format.fprintf Format.std_formatter "\r";
  Format.fprintf Format.std_formatter
    ("%a%a@[<hov>" ^^ format ^^ "@]@.")
    (pp_time ~lvl) section
    Level.prefix lvl

let aux ?(section=Section.root) lvl format =
  let cur_lvl = Section.cur_level section in
  if Level.compare lvl cur_lvl <= 0 then
    pp_aux ~section ~lvl format
  else
    Format.ifprintf Format.std_formatter format

let log ?section = aux ?section Level.log
let error ?section = aux ?section Level.error
let warn ?section = aux ?section Level.warn
let info ?section = aux ?section Level.info
let debug ?section = aux ?section Level.debug


(* Profiling *)
(* ************************************************************************ *)

let enter_prof = Section.enter
let exit_prof = Section.exit

let within_prof section f arg =
  enter_prof section;
  match f arg with
  | res ->
    exit_prof section;
    res
  | exception exn ->
    exit_prof section;
    raise exn

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


