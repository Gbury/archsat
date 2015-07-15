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
let get_total_time =
  let start = Unix.gettimeofday () in
  (function () ->
    let stop = Unix.gettimeofday () in
    stop -. start)

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
    mutable level : int;
    mutable profile : bool; (* should this section be profiled *)
    mutable prof_in : bool; (* are we currently inside the profiler of this section *)
    mutable prof_enter : float; (* time of last entry of the profiler *)
    mutable prof_total : float;
    mutable full_name : string;
  }

  and descr =
    | Root
    | Sub of string * t * t list  (* name, parent, inheriting *)

  let root= {
    descr = Root;
    level = 0;
    profile = false;
    prof_in = false;
    prof_enter = 0.;
    prof_total = 0.;
    full_name = "";
  }

  module type S = sig
    val section : t
  end

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

  let short_name s = match s.descr with
    | Root -> "root"
    | Sub (name, _, _) -> name

  (* full name -> section *)
  let nb_section = ref 1
  let section_table = Hashtbl.create 15
  let section_children = Hashtbl.create 15

  let get_children s =
    try Hashtbl.find section_children s.full_name
    with Not_found ->
      let l = ref [] in
      Hashtbl.add section_children s.full_name l;
      l

  let set_debug s i = s.level <- if i < 0 then null_level else i
  let clear_debug s = s.level <- null_level
  let get_debug s =
    if s.level=null_level then None else Some s.level

  let make ?(parent=root) ?(inheriting=[]) name =
    if name = "" then invalid_arg "Section.make: empty name";
    let sec = {
      descr = Sub (name, parent, inheriting);
      level = null_level;
      profile = false;
      prof_in = false;
      prof_enter = 0.;
      prof_total = 0.;
      full_name="";
    } in
    let name' = compute_full_name sec in
    try
      Hashtbl.find section_table name'
    with Not_found ->
      (* new section! register it, add an option to set its level *)
      incr nb_section;
      sec.full_name <- name';
      Hashtbl.add section_table name' sec;
      let l = get_children parent in
      l := sec:: !l;
      sec

  (* Iter through sections *)
  let iter yield =
    yield ("", root);
    Hashtbl.iter (fun name sec -> yield (name,sec)) section_table

  let find name = Hashtbl.find section_table name

  (* recursive lookup, with inheritance from parent *)
  let rec cur_level_rec s =
    if s.level = null_level
    then match s.descr with
      | Root -> null_level
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

  (* Entering a profiler *)
  let prof_enter s =
    s.prof_enter <- get_total_time ();
    s.prof_in <- true

  let rec prof_exit_aux s time =
    if not s.prof_in then begin
      s.prof_total <- s.prof_total +. time;
      begin match s.descr with
        | Root -> true
        | Sub (_, s', _) -> prof_exit_aux s' time
      end
    end else
      false

  let prof_exit s =
    let time = get_total_time () in
    if s.prof_in then begin
      let increment = time -. s.prof_enter in
      s.prof_in <- false;
      prof_exit_aux s increment
    end else
      true

  (** Activate profiling for a section (and its children) *)
  let rec profile_section s =
    s.profile <- true;
    List.iter profile_section !(get_children s)

  let rec profile_depth d s =
    s.profile <- d >= 0;
    List.iter (profile_depth (d - 1)) !(get_children s)

  let set_profile_depth d =
    if d <= 0 then profile_section root
    else profile_depth d root
end

(* Debug output functions *)
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

(** {2 profiling facilities} *)


(** Global switch for profiling *)
let active = ref []

let curr () = match !active with
  | s :: _ -> Some s | [] -> None

(** Enter the profiler *)
let rec is_parent_active s =
  s.Section.prof_in ||
  (match s.Section.descr with
   | Section.Root -> false
   | Section.Sub (_, s', _) -> is_parent_active s')

let enter_prof section =
  if section.Section.profile then begin
    match !active with
    | s :: _ when s == section ->
      active := section :: !active
    | _ ->
      if not (is_parent_active section) then
        ignore (CCOpt.map Section.prof_exit (curr ()));
      Section.prof_enter section;
      active := section :: !active
  end

(** Exit the profiler *)
let exit_prof section =
  if section.Section.profile then begin
    match !active with
    | s :: r ->
      assert (s == section);
      let b = Section.prof_exit section in
      active := r;
      begin match r with
        | [] -> ()
        | s' :: _ -> if b then Section.prof_enter s'
      end
    | [] -> assert false
  end

(** Print the profiler results *)
let parent_time s =
  match s.Section.descr with
  | Section.Root -> s.Section.prof_total
  | Section.Sub (_, s', _) -> s'.Section.prof_total

let rec section_tree s =
  if s.Section.prof_total < (parent_time s) /. 100. then `Empty
  else begin
    let l = !(Section.get_children s) in
    let l' = List.sort (fun s' s'' -> Section.(compare s''.prof_total s'.prof_total)) l in
    `Tree(s , List.map section_tree l')
  end

let rec flatten = function
  | `Empty -> []
  | `Tree (x, l) -> x :: CCList.flatten (List.map flatten l)

let rec map_tree f = function
  | `Empty -> `Empty
  | `Tree (x, l) -> `Tree (f x, List.map (map_tree f) l)

let print_profiler () =
  if !active <> [] then begin
    debug 0 "Debug sections not closed properly";
    while !active <> [] do
      debug 0 "Closing section %s forcefully" (List.hd !active).Section.full_name;
      exit_prof (List.hd !active)
    done;
  end;
  let total_time = get_total_time () in
  let s_tree = section_tree Section.root in
  let tree_box = Containers_misc.PrintBox.(
      Simple.to_box (map_tree (fun s -> `Text (Section.short_name s)) s_tree)) in
  let time_box = Containers_misc.PrintBox.(vlist ~bars:false (flatten (
      map_tree (fun s -> text (Format.sprintf "%13.3f" s.Section.prof_total)) s_tree))) in
  let rate_box = Containers_misc.PrintBox.(vlist ~bars:false (flatten (
      map_tree (fun s -> text (Format.sprintf "%6.2f%%" (
          s.Section.prof_total /. total_time *. 100.))) s_tree))) in
  let b = Containers_misc.PrintBox.(
      grid ~pad:(hpad 3) ~bars:true [|
        [| text "Section name"; text "Time profiled"; text "Profiled rate" |];
        [| text "Total Time"; text (Format.sprintf "%13.3f" total_time); text "100.00%" |];
        [| tree_box; time_box; rate_box |];
      |]) in
  Containers_misc.PrintBox.output stdout b

let enable_profiling () =
  Section.profile_section Section.root;
  at_exit print_profiler

(** {2 LogtkOrdering utils} *)

let rec lexicograph f l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | x::xs, y::ys ->
    let c = f x y in
    if c <> 0 then c else lexicograph f xs ys
  | [],_ -> (-1)
  | _,[] -> 1

(** {2 List util} *)

let list_iteri2 f l l' =
  let rec aux i f l l' = match l, l' with
    | x :: r, y :: r' ->
      f i x y; aux (i + 1) f r r'
    | [], [] -> ()
    | _ -> invalid_arg "list_iteri2"
  in
  aux 0 f l l'
