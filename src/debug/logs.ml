(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Types *)
(* ************************************************************************ *)

type t = {
  time    : int64;
  section : Section.t;
  lvl     : Level.t;
  msg     : string;
}

type log = t CCVector.vector

(* Manipulating logs *)
(* ************************************************************************ *)

let dummy = {
  time = 0L;
  msg = "";
  lvl = Level.log;
  section = Section.root;
}

let make ~section ~lvl msg =
  let time = Time.get_total_clock () in
  { time; msg; lvl; section; }

(* Log storage *)
(* ************************************************************************ *)

let tbl : log = CCVector.create_with ~capacity:4096 dummy

let add ~section ~lvl msg =
  CCVector.push tbl (make ~section ~lvl msg)

let log ~section ~lvl format =
  CCFormat.ksprintf ~f:(add ~section ~lvl) format

(* Log access *)
(* ************************************************************************ *)

let get = CCVector.get tbl
let length () = CCVector.length tbl

