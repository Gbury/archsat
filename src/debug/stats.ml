(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

exception Out_of_stats

(* Debug output functions *)
(* ************************************************************************ *)

type t = {
  name  : string;
  index : int;
}

let eq t t' = t.index = t'.index

let mk =
  let curr = ref ~-1 in
  (fun name ->
     if !curr >= Section.max_stats then
       raise Out_of_stats
     else begin
       incr curr;
       { name; index = !curr }
     end)

let get t s = (Section.stats s).(t.index)
let set t s v = (Section.stats s).(t.index) <- v

let incr ?(k=1) t s =
  let i = t.index in
  let a = Section.stats s in
  a.(i) <- a.(i) + k

(* Stats groups *)
(* ************************************************************************ *)

type group = {
  mutable stats : t list;
  mutable sections : Section.t list;
}

let all_groups = ref []

let bundle stats =
  let res = { stats; sections = [] } in
  all_groups := res :: !all_groups;
  res

let add_to_group group stat =
  group.stats <- CCList.add_nodup ~eq stat group.stats

let attach t group =
  group.sections <- CCList.add_nodup ~eq:Section.equal t group.sections

(* Print statistics *)
(* ************************************************************************ *)

let ignore_group g =
  g.sections = [] || g.stats = [] || (
    List.for_all (fun s ->
        List.for_all (fun stat ->
            get stat s = 0
          ) g.stats
    ) g.sections
  )

let print_stats_group g =
  if ignore_group g then ()
  else begin
    let l = "Sections" :: (List.map (fun s -> s.name) g.stats) in
    let sections = PrintBox.(vlist ~bars:false (
        List.map (fun s -> text (Section.full_name s)) g.sections)) in
    let stats = List.map (fun t -> PrintBox.(vlist ~bars:false (
        List.map (fun s -> int_ @@ get t s) g.sections))) g.stats in
    let b = PrintBox.(
        grid ~pad:(hpad 3) ~bars:true [|
          Array.of_list (List.map (fun s -> text s) l);
          Array.of_list (sections :: stats);
        |]) in
    print_newline ();
    PrintBox.output stdout b
  end

let print () =
  List.iter print_stats_group !all_groups

