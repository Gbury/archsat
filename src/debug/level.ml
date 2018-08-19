(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Level definition *)
(* ************************************************************************ *)

type t =
  | Null
  | Error
  | Warn
  | Log
  | Info
  | Debug

let equal (x: t) y = x = y

let compare (x: t) y = compare x y

let max (x: t) y = max x y

(* Logging levels *)
(* ************************************************************************ *)

let null = Null
let error = Error
let warn = Warn
let log = Log
let info = Info
let debug = Debug

(* Colors for logging *)
(* ************************************************************************ *)

let prefix fmt = function
  | Error -> CCFormat.with_colorf "Red" fmt "[ERROR] "
  | Warn -> CCFormat.with_colorf "Magenta" fmt "[WARNING] "
  | _ -> ()

(* Conversions *)
(* ************************************************************************ *)

let to_string = function
  | Null -> "null"
  | Error -> "error"
  | Warn -> "warn"
  | Log -> "log"
  | Info -> "info"
  | Debug -> "debug"

