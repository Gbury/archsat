
(* Level definition *)
(* ************************************************************************ *)

type t = int

let equal (x: int) y = x = y

let compare (x: int) y = compare x y

let max (x: int) y = max x y

(* Logging levels *)
(* ************************************************************************ *)

let null = -2

let error = -1

let log = 0

let warn = 1

let info = 5

let debug = 10

