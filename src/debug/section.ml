
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
  mutable prof_enter : Int64.t; (* time of last entry of the profiler *)
  mutable prof_total : Int64.t; (* total time elasped inside the profiler *)

  mutable nb_calls : int;
  mutable full_name : string;
}

and descr =
  | Root
  | Sub of string * t * t list  (* name, parent, inheriting *)

(* Usual functions *)
(* ************************************************************************ *)

let equal s s' = s.full_name = s'.full_name
let compare s s' = compare s.full_name s'.full_name
let hash { full_name; _ } = Hashtbl.hash full_name

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

(* Association tables *)
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

(* Debug levels *)
(* ************************************************************************ *)

let set_debug s i = s.level <- i

let get_debug s =
  if s.level = Level.null then None else Some (s.level)

let clear_debug s =
  s.level <- Level.null

(* Creating sections *)
(* ************************************************************************ *)

let root = {
  descr = Root;
  level = Level.log;
  stats = Array.make max_stats 0;
  profile = false;
  prof_in = false;
  prof_enter = 0L;
  prof_total = 0L;
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
    prof_enter = 0L;
    prof_total = 0L;
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

(* Iter through sections *)
let iter yield =
  yield ("", root);
  Hashtbl.iter (fun name sec -> yield (name,sec)) section_table

let find name = Hashtbl.find section_table name

(* recursive lookup, with inheritance from parent *)
let rec cur_level_rec s =
  if s.level = Level.null then
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
  if s.level = Level.null then
    let r = cur_level_rec s in
    set_debug s r;
    r
  else
    s.level

(* Profiling *)
(* ************************************************************************ *)

let prof_enter s =
  s.prof_enter <- Time.get_total_clock ();
  s.nb_calls <- s.nb_calls + 1;
  s.prof_in <- true

let rec prof_exit_aux s time =
  if not s.prof_in then begin
    s.prof_total <- Int64.add s.prof_total time;
    begin match s.descr with
      | Root -> true
      | Sub (_, s', _) -> prof_exit_aux s' time
    end
  end else
    false

let prof_exit s =
  let time = Time.get_total_clock () in
  if s.prof_in then begin
    let increment = Int64.sub time s.prof_enter in
    s.prof_in <- false;
    prof_exit_aux s increment
  end else
    true

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

