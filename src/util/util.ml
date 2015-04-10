(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 Some helpers} *)

(** {2 Time facilities} *)

(** Time elapsed since initialization of the program, and time of start *)
let get_total_time, get_start_time =
  let start = Unix.gettimeofday () in
  (function () ->
    let stop = Unix.gettimeofday () in
    stop -. start),
  (function () -> start)

(** {2 Misc} *)

let clear_line () =
  output_string Pervasives.stdout
    "\r                                                         \r";
  flush Pervasives.stdout

(** Debug section *)
module Section = struct
  let null_level = -1 (* absence of level *)
  type t = {
    descr : descr;
    mutable full_name : string;
    mutable level : int;
  }
  and descr =
    | Root
    | Sub of string * t * t list  (* name, parent, inheriting *)

  let root={descr=Root; full_name=""; level=0; }

  (* computes full name of section *)
  let compute_full_name s =
    let buf = Buffer.create 15 in
    let rec add s = match s.descr with
      | Root -> true
      | Sub (name, parent, _) ->
        let parent_is_root = add parent in
        if not parent_is_root then Buffer.add_char buf '.';
        Buffer.add_string buf name;
        false
    in
    ignore (add s);
    Buffer.contents buf

  let full_name s = s.full_name

  (* full name -> section *)
  let section_table = Hashtbl.create 15

  let set_debug s i = s.level <- if i < 0 then null_level else i
  let clear_debug s = s.level <- null_level
  let get_debug s =
    if s.level=null_level then None else Some s.level

  let make ?(parent=root) ?(inheriting=[]) name =
    if name="" then invalid_arg "Section.make: empty name";
    let sec = {
      descr=Sub(name, parent, inheriting);
      full_name="";
      level=null_level;
    } in
    let name' = compute_full_name sec in
    try
      Hashtbl.find section_table name'
    with Not_found ->
      (* new section! register it, add an option to set its level *)
      sec.full_name <- name';
      Hashtbl.add section_table name' sec;
      sec

  let iter yield =
    yield ("", root);
    Hashtbl.iter (fun name sec -> yield (name,sec)) section_table

  let find name = Hashtbl.find section_table name

  (* recursive lookup, with inheritance from parent *)
  let rec cur_level_rec s =
    if s.level = null_level
    then match s.descr with
      | Root -> -1
      | Sub (_, parent, []) -> cur_level_rec parent
      | Sub (_, parent, [i]) -> max (cur_level_rec parent) (cur_level_rec i)
      | Sub (_, parent, inheriting) ->
        List.fold_left
          (fun m i -> max m (cur_level_rec i))
          (cur_level_rec parent) inheriting
    else s.level

  (* inlinable function *)
  let cur_level s =
    if s.level = null_level
    then cur_level_rec s
    else s.level
end

let set_debug = Section.set_debug Section.root
let get_debug () = Section.root.Section.level
let need_cleanup = ref false

let debug_buf_ = Buffer.create 32 (* shared buffer (not thread safe)  *)
let debug ?(section=Section.root) l format =
  if l <= Section.cur_level section
  then (
    Buffer.clear debug_buf_;
    if !need_cleanup then clear_line ();
    (* print header *)
    let now = get_total_time () in
    if section == Section.root
    then Printf.bprintf debug_buf_ "%% [%.3f] " now
    else Printf.bprintf debug_buf_ "%% [%.3f %s] "
        now section.Section.full_name;
    Printf.kbprintf
      (fun b -> Buffer.output_buffer stdout b; print_char '\n'; flush stdout)
      debug_buf_ format)
  else
    Printf.ifprintf debug_buf_ format

let pp_pos pos =
  let open Lexing in
  Printf.sprintf "line %d, column %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)

(** {2 profiling facilities} *)

(** A profiler (do not call recursively) *)
type profiler = {
  prof_name : string;
  mutable prof_total : float;   (** total time *)
  mutable prof_calls : int;     (** number of calls *)
  mutable prof_max : float;     (** max time in the profiled function *)
  mutable prof_enter : float;   (** time at which we entered the profiler *)
}

(** Global switch for profiling *)
let enable_profiling = ref false

(** all profilers *)
let profilers = ref []

(** create a named profiler *)
let mk_profiler name =
  let prof = {
    prof_enter = 0.;
    prof_name = name;
    prof_total = 0.;
    prof_calls = 0;
    prof_max = 0.;
  } in
  (* register profiler *)
  profilers := prof :: !profilers;
  prof

(** Enter the profiler *)
let enter_prof profiler =
  if !enable_profiling then profiler.prof_enter <- Unix.gettimeofday ()

(** Exit the profiled code with a value *)
let exit_prof profiler =
  if !enable_profiling then begin
    let stop = Unix.gettimeofday () in
    let delta = stop -. profiler.prof_enter in
    profiler.prof_total <- profiler.prof_total +. delta;
    profiler.prof_calls <- profiler.prof_calls + 1;
    (if delta > profiler.prof_max then profiler.prof_max <- delta);
  end

(* difference with [exit_prof]: does not increment the total count *)
let yield_prof profiler =
  if !enable_profiling then begin
    let stop = Unix.gettimeofday () in
    let delta = stop -. profiler.prof_enter in
    profiler.prof_total <- profiler.prof_total +. delta;
    (if delta > profiler.prof_max then profiler.prof_max <- delta);
  end

(** Print profiling data upon exit *)
let () =
  at_exit (fun () ->
      if !enable_profiling && List.exists (fun profiler -> profiler.prof_calls > 0) !profilers
      then begin
        Printf.printf "%% %39s ---------- --------- --------- --------- ---------\n"
          (String.make 39 '-');
        Printf.printf "%% %-39s %10s %9s %9s %9s %9s\n" "function" "#calls"
          "total" "% total" "max" "average";
        (* sort profilers by name *)
        let profilers = List.sort
            (fun p1 p2 -> String.compare p1.prof_name p2.prof_name)
            !profilers in
        let tot = get_total_time () in
        List.iter
          (fun profiler -> if profiler.prof_calls > 0 then
              (* print content of the profiler *)
              Printf.printf "%% %-39s %10d %9.4f %9.2f %9.4f %9.4f\n"
                profiler.prof_name profiler.prof_calls profiler.prof_total
                (profiler.prof_total *. 100. /. tot) profiler.prof_max
                (profiler.prof_total /. (float_of_int profiler.prof_calls)))
          profilers
      end)

(** {2 Runtime statistics} *)

type stat = string * int64 ref 

let mk_stat, print_global_stats =
  let stats = ref [] in
  (* create a stat *)
  (fun name ->
     let stat = (name, ref 0L) in
     stats := stat :: !stats;
     stat),
  (* print stats *)
  (fun () ->
     let stats = List.sort (fun (n1,_)(n2,_) -> String.compare n1 n2) !stats in
     List.iter
       (fun (name, cnt) ->
          debug 0 "stat: %-30s ... %s" name (Int64.to_string !cnt))
       stats)

let incr_stat (_, count) = count := Int64.add !count Int64.one  (** increment given statistics *)
let add_stat (_, count) num = count := Int64.add !count (Int64.of_int num) (** add to stat *)

(** {2 LogtkOrdering utils} *)

let rec lexicograph f l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | x::xs, y::ys ->
    let c = f x y in
    if c <> 0 then c else lexicograph f xs ys
  | [],_ -> (-1)
  | _,[] -> 1

