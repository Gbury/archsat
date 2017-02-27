
(* Types *)
(* ************************************************************************ *)

type t = {
  time : int64;
  msg : string;
  lvl : Util.Level.t;
}

type log = t CCVector.vector

(* Manipulating logs *)
(* ************************************************************************ *)

let dummy = {
  time = 0L;
  msg = "";
  lvl = Util.Level.log;
}

(* Log storage *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Util.Section)

let tbl = Hashtbl.create 137

let get_logs s =
  try Hashtbl.find tbl s
  with Not_found ->
    let v = CCVector.create () in
    Hashtbl.add tbl s v;
    v

