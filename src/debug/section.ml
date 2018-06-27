
(* Magic constant *)
(* ************************************************************************ *)

let max_stats = 100

(* Debugging Section *)
(* ************************************************************************ *)

type t = {
  descr : descr;
  mutable level : Level.t;
  mutable stats : int array;

  mutable profile : bool; (* should this section be profiled *)
  mutable prof_in : bool; (* are we currently inside the profiler of this section *)
  mutable prof_total : Mtime.span; (* total time elasped inside the profiler *)
  mutable prof_enter : Mtime_clock.counter; (* time of last entry of the profiler *)

  mutable nb_calls : int;
  mutable full_name : string;
}

and descr =
  | Root
  | Sub of string * t * t list  (* name, parent, inheriting *)

(* Access functions *)
(* ************************************************************************ *)

let equal s s' = s.full_name = s'.full_name
let compare s s' = compare s.full_name s'.full_name
let hash { full_name; _ } = Hashtbl.hash full_name

let stats { stats; _ } = stats

(* Section names *)
(* ************************************************************************ *)

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


(* Logging *)
(* ************************************************************************ *)

let set_debug s i = s.level <- i

let get_debug s =
  if s.level = Level.null then None else Some (s.level)

let clear_debug s =
  s.level <- Level.null

(* recursive lookup, with inheritance from parent *)
let rec cur_level_rec s =
  if Level.equal s.level Level.null then
    match s.descr with
    | Root -> Level.error
    | Sub (_, parent, []) -> cur_level_rec parent
    | Sub (_, parent, [i]) -> max (cur_level_rec parent) (cur_level_rec i)
    | Sub (_, parent, inheriting) ->
      List.fold_left
        (fun m i -> max m (cur_level_rec i))
        (cur_level_rec parent) inheriting
  else
    s.level

(* inlinable function *)
let cur_level s =
  if Level.equal s.level Level.null then
    let r = cur_level_rec s in
    set_debug s r;
    r
  else
    s.level


(* Creating sections *)
(* ************************************************************************ *)

let nb_section = ref 1
let section_table = Hashtbl.create 47
let section_children = Hashtbl.create 47

let get_children s =
  try Hashtbl.find section_children s.full_name
  with Not_found ->
    let l = ref [] in
    Hashtbl.add section_children s.full_name l;
    l

let root = {
  descr = Root;
  level = Level.log;
  stats = Array.make max_stats 0;
  profile = false;
  prof_in = false;
  prof_total = Mtime.Span.zero;
  prof_enter = Mtime_clock.counter ();
  nb_calls = 0;
  full_name = "";
}

let make ?(parent=root) ?(inheriting=[]) name =
  if name = "" then invalid_arg "Section.make: empty name";
  let sec = {
    descr = Sub (name, parent, inheriting);
    level = Level.null;
    stats = Array.make max_stats 0;
    profile = false;
    prof_in = false;
    prof_total = Mtime.Span.zero;
  prof_enter = Mtime_clock.counter ();
    nb_calls= 0;
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

let find = Hashtbl.find section_table

let iter yield =
  yield root;
  Hashtbl.iter (fun _ s -> yield s) section_table

(* Profiling *)
(* ************************************************************************ *)

(* Base functions for profiling.

   Entering a profiled section is simple. When exiting, we go up the parent
   chain to add the profiled time, until an actively profiled section is
   encountered; this is done so that a section always contain the profiled time
   of all its subsections, even if the sections were not explicitly entered.
*)
let prof_enter s =
  s.prof_enter <- Mtime_clock.counter ();
  s.nb_calls <- s.nb_calls + 1;
  s.prof_in <- true

let rec prof_exit_aux s time =
  if not s.prof_in then begin
    s.prof_total <- Mtime.Span.add s.prof_total time;
    begin match s.descr with
      | Root -> true
      | Sub (_, s', _) -> prof_exit_aux s' time
    end
  end else
    false

let prof_exit s =
  if s.prof_in then begin
    let increment = Mtime_clock.count s.prof_enter in
    s.prof_enter <- Mtime_clock.counter (); (* just in case, avoid double timing *)
    s.prof_in <- false;
    prof_exit_aux s increment
  end else
    true


(* High level profiling.

   The idea is to allow to allow context switch:
   Imagine that there are two unrelated sections A and B,
   while profiling A, we want to call a function we want profiled
   in section B. In order for the time spent in B not to be counted
   for A, we maintain a list of entered sections that have not yet
   eded profiling, but that we exited because of a context switch.
  *)

let active = ref []

let curr () =
  match !active with
  | s :: _ -> Some s | [] -> None

let rec is_parent_active s =
  s.prof_in || (
    match s.descr with
    | Root -> false
    | Sub (_, s', _) -> is_parent_active s'
  )

(** Enter the profiler *)
let enter section =
  if section.profile then begin
    match !active with
    | s :: _ when s == section ->
      active := section :: !active
    | _ ->
      if not (is_parent_active section) then
        ignore (CCOpt.map prof_exit (curr ()));
      prof_enter section;
      active := section :: !active
  end

(** Exit the profiler *)
let exit section =
  if section.profile then begin
    match !active with
    | s :: r ->
      assert (s == section);
      let b = prof_exit section in
      active := r;
      begin match r with
        | [] -> ()
        | s' :: _ -> if b then prof_enter s'
      end
    | [] -> assert false
  end

(* Profile activation *)
(* ************************************************************************ *)

let rec profile_section s =
  s.profile <- true;
  List.iter profile_section !(get_children s)

let rec profile_depth d s =
  s.profile <- d >= 0;
  List.iter (profile_depth (d - 1)) !(get_children s)

let set_profile_depth d =
  if d <= 0 then profile_section root
  else profile_depth d root

(* Profiling info printing *)
(* ************************************************************************ *)

let parent_time s =
  match s.descr with
  | Root -> s.prof_total
  | Sub (_, s', _) -> s'.prof_total

let rec section_tree test s =
  if not (test s) then `Empty
  else begin
    let l = !(get_children s) in
    let l' = List.sort (fun s' s'' ->
        Mtime.Span.compare s''.prof_total s'.prof_total
      ) l in
    `Tree(s , List.map (section_tree test) l')
  end

let rec flatten = function
  | `Empty -> []
  | `Tree (x, l) -> x :: CCList.flatten (List.map flatten l)

let rec map_tree f = function
  | `Empty -> `Empty
  | `Tree (x, l) -> `Tree (f x, List.map (map_tree f) l)

let print_profiling_info () =
  let total_time = Mtime_clock.elapsed () in
  let s_tree = section_tree (fun s ->
      (Mtime.Span.to_ns s.prof_total) > ((Mtime.Span.to_ns @@ parent_time s) /. 100.)
    ) root in
  let tree_box = PrintBox.(
      Simple.to_box (map_tree (fun s -> `Text (short_name s)) s_tree)) in
  let call_box = PrintBox.(vlist ~bars:false (flatten (
      map_tree (fun s -> text (Format.sprintf "%10d" s.nb_calls)) s_tree))) in
  let time_box = PrintBox.(vlist ~bars:false (flatten (
      map_tree (fun s -> text (Format.asprintf "%a" Mtime.Span.pp s.prof_total)) s_tree))) in
  let rate_box = PrintBox.(vlist ~bars:false (flatten (
      map_tree (fun s -> text (Format.sprintf "%6.2f%%" (
          (Mtime.Span.to_ms s.prof_total) /. (Mtime.Span.to_ms total_time) *. 100.))) s_tree))) in
  let b = PrintBox.(
      grid ~pad:(hpad 3) ~bars:true [|
        [| text "Section name"; text "Time profiled"; text "Profiled rate"; text "Calls" |];
        [| text "Total Time"; text (Format.asprintf "%a" Mtime.Span.pp total_time); text "100.00%"; text "N/A" |];
        [| tree_box; time_box; rate_box; call_box |];
      |]) in
  print_newline ();
  PrintBox.output stdout b

let csv_prof_data fmt =
  let tree = section_tree (fun _ -> true) root in
  List.iter (fun s ->
      let name = match full_name s with "" -> "root" | s -> s in
      Format.fprintf fmt "%s,%f@." name (Mtime.Span.to_ns s.prof_total)
    ) (flatten tree)


