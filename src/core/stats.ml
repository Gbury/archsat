
let log_section = Util.Section.make "stats"
let log i fmt = Util.debug ~section:log_section i fmt

(* Statistics record & manipulations *)
type t = {
  mutable cur_round : int;
  instanciations : ((int * int), CCVector.rw) CCVector.t;
}

let print_state state =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  log 0 "Round %d : instanciations %d (remaining : %d)" s i r

let init_round state =
  state.cur_round <- state.cur_round + 1;
  CCVector.push state.instanciations (0, 0)

(* State record *)
let state = {
  cur_round = 0;
  instanciations = CCVector.make 1 (0, 0);
  }

(* Exported functions *)
let current_round () = state.cur_round

let inst_done () =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i + 1, r)

let inst_remaining r =
  let s = state.cur_round in
  let (i, _) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i, r)

(* Print stats and prep for next round *)
let clock _ =
  print_state state;
  init_round state

;;
Dispatcher.(register (
  mk_ext
    ~descr:"Handles delayed printing of statistics for each round of solving"
    ~prio:~-10 ~if_sat:clock
    (new_id ()) "stats"
))

