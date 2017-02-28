
(* Debug output functions *)
(* ************************************************************************ *)

type t = {
  name  : string;
  index : int;
}

let mk =
  let curr = ref ~-1 in
  (fun name -> incr curr; { name; index = !curr })

let get t s = (Section.stats s).(t.index)
let set t s v = (Section.stats s).(t.index) <- v

let incr ?(k=1) t s =
  let i = t.index in
  let a = Section.stats s in
  a.(i) <- a.(i) + k

(* Stats groups *)
(* ************************************************************************ *)

type group = {
  stats : t list;
  mutable sections : Section.t list;
}

let all_groups = ref []

let bundle stats =
  let res = { stats; sections = [] } in
  all_groups := res :: !all_groups;
  res

let attach t group =
  group.sections <- CCList.add_nodup ~eq:Section.equal t group.sections

(* Print statistics *)
(* ************************************************************************ *)

let print_stats_group g =
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

let print () =
  List.iter print_stats_group !all_groups

