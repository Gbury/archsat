
let section = Util.Section.make ~parent:Dispatcher.section "stats"

(* Options *)
(* ************************************************************************ *)

let max_rounds = ref 0

(* Statistics accumulator *)
(* ************************************************************************ *)

type t = {
  mutable cur_round : int;
  instanciations : ((int * int), CCVector.rw) CCVector.t;
}

let print_state state =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  if i > 0 || r > 0 then
    Util.log ~section "Round %d : instanciations %d (remaining : %d)"
      (fun k -> k s i r)

let init_round state =
  state.cur_round <- state.cur_round + 1;
  CCVector.push state.instanciations (0, 0)

(* State record *)
let state = {
  cur_round = 0;
  instanciations = CCVector.make 1 (0, 0);
  }

(* Exported functions *)
(* ************************************************************************ *)

let current_round () = state.cur_round

let inst_done k =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i + k, r)

let inst_remaining r =
  let s = state.cur_round in
  let (i, _) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i, r)

(* Print stats and prep for next round *)
let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dispatcher.If_sat _ ->
    print_state state;
    if !max_rounds >= 0 && state.cur_round >= !max_rounds then
      raise (Extension.Abort (
          "stats", Format.sprintf "Maximum number of rounds reached (%d)" !max_rounds));
    init_round state;
    Some ()
  | _ -> None

(* Extension registering *)
(* ************************************************************************ *)

let options =
  let docs = Options.ext_sect in
  let stop =
    let doc = "Stop at the given round" in
    Cmdliner.Arg.(value & opt int (-1) & info ["stats.stop"] ~docv:"N" ~docs ~doc)
  in
  let set_opts n =
    max_rounds := n
  in
  Cmdliner.Term.(pure set_opts $ stop)

let register () =
  Dispatcher.Plugin.register "stats" ~prio:0 ~options
    ~descr:"Handles delayed printing of statistics for each round of solving"
    (Dispatcher.mk_ext
       ~handle:{Dispatcher.handle = handle }
       ~section ()
    )

