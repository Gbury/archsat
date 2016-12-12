
(* GC alarm for time/space limits *)
(* ************************************************************************ *)

(* This function analyze the current size of the heap *)
let check size_limit = function () ->
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if s > size_limit then
    raise Options.Out_of_space

(* There are two kinds of limits we want to enforce:
   - a size limit: we use the Gc's alarm function to enforce the limit
     on the size of the RAM used
   - a time limit: the Gc alarm is not reliable to enforce this, so instead
     we use the Unix.timer facilities *)
let setup_alarm t s =
  let _ = Unix.setitimer Unix.ITIMER_REAL
      Unix.{it_value = t; it_interval = 0.01 } in
  Gc.create_alarm (check s)

let delete_alarm alarm =
  let _ = Unix.setitimer Unix.ITIMER_REAL
      Unix.{it_value = 0.; it_interval = 0. } in
  Gc.delete_alarm alarm

(* The Unix.timer works by sending a Sys.sigalrm, so in order to use it,
   we catch it and raise the Out_of_time exception. *)
let () =
  Sys.set_signal Sys.sigalrm (
    Sys.Signal_handle (fun _ ->
      Util.need_cleanup := true;
      raise Options.Out_of_time)
  )

(* We also want to catch user interruptions *)
let () =
  Sys.set_signal Sys.sigint (
    Sys.Signal_handle (fun _ ->
      Util.need_cleanup := true;
      raise Options.Sigint)
    )

(* Pipeline and execution *)
(* ************************************************************************ *)

type 'a gen = 'a Gen.t
type opt = Options.copts
type ('a, 'b) f = 'a -> 'b

type (_, _) t =
  | End :
      ('a, 'a) t
  | Map :
      ('a, 'c) f * ('c, 'b) t -> ('a, 'b) t
  | Expand :
      ('opt * 'a, 'opt * [< `Single of 'c | `Gen of bool * 'c gen]) f *
      ('opt * 'c, 'opt) t -> ('opt * 'a, 'opt) t

let pipe = End
let map f t = Map (f, t)
let expand f t = Expand(f, t)

let rec eval : type a b. (a, b) t -> (a, b) f =
  fun pipe x ->
    match pipe with
    | End -> x
    | Map (f, t) ->
      eval t (f x)
    | Expand (f, t) ->
      match f x with
      | opt, `Single y ->
        eval t (opt, y)
      | opt, `Gen (flat, g) ->
        let aux opt c = eval t (opt, c) in
        let opt' = Gen.fold aux opt g in
        if flat then (fst x) else opt'

let run_aux : type a. (opt * a, opt) t -> a gen -> opt -> opt option =
  fun pipe g opt ->
    match g () with
    | None -> None
    | Some x ->
      Some (eval pipe (opt, x))

let rec run : type a. (opt * a, opt) t -> a gen -> opt -> unit =
  fun pipe g opt ->
    let time = opt.Options.time_limit in
    let size = opt.Options.size_limit in
    let al = setup_alarm time size in
    begin
      match run_aux pipe g opt with
      | None ->
        delete_alarm al
      | Some opt' ->
        delete_alarm al;
        run pipe g opt'
      | exception exn ->
        delete_alarm al;
        if Printexc.backtrace_status () then
          Printexc.print_backtrace stdout;
        Out.print_exn opt exn;
        run pipe g opt
    end

