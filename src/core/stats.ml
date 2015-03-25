
let log_section = Util.Section.make "stats"
let log i fmt = Util.debug ~section:log_section i fmt

(* Statistics record & manipulations *)
type t = {
  mutable cur_round : int;
  instanciations : (int * int) Vector.t;
}

let print_state state =
  let s = state.cur_round in
  let (i, r) = Vector.get state.instanciations s in
  log 0 "Round %d : instanciations %d (remaining : %d)" s i r

let init_round state i =
  state.cur_round <- i;
  Vector.set state.instanciations i (0, 0)

(* State record *)
let state = {
  cur_round = 0;
  instanciations = Vector.make 64 (0, 0);
  }

let () = init_round state 0 (* Initialization for round 0 *)

(* Exported functions *)
let inst_done () =
  let s = state.cur_round in
  let (i, r) = Vector.get state.instanciations s in
  Vector.set state.instanciations s (i + 1, r)

let inst_remaining r =
  let s = state.cur_round in
  let (i, _) = Vector.get state.instanciations s in
  Vector.set state.instanciations s (i, r)

(* Print stats and prep for next round *)
let clock _ =
  print_state state;
  let i = state.cur_round + 1 in
  init_round state i

;;
Dispatcher.(register (
  mk_ext
    ~descr:"Handles delayed printing of statistics for each round of solving"
    ~prio:~-10 ~if_sat:clock
    (new_id ()) "stats"
))

