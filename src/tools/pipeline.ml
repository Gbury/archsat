
(* Default exception handler *)
(* ************************************************************************ *)

let default_handler opt exn =
  Format.eprintf "Exception: @<hov>%s@]@." (Printexc.to_string exn)

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

(** Some aliases for readibility *)
type 'a gen = 'a Gen.t
type opt = Options.copts
type ('a, 'b) f = 'a -> 'b

(** Type for pipelines, i.e a serie of functions to
    apply to the input. An ('a, 'b) t is a pipeline that
    takes an input of type ['a] and returns a value of type
    ['b]. *)
type (_, _) t =
  (** The end of the pipeline, the identity/reflexive constructor *)
  | End :
      ('a, 'a) t
  (** A simple function to apply. *)
  | Map :
      ('a, 'c) f * ('c, 'b) t -> ('a, 'b) t
  (** Expand a single input into a generator of outputs.
      The base idea is to fold the inner pipeline over the generator. *)
  | Expand :
      ('opt * 'a, 'opt * [< `Single of 'c | `Gen of bool * 'c gen]) f *
      ('opt * 'c, 'opt) t -> ('opt * 'a, 'opt) t

(** Creating pipelines.
    TODO: better functions/infix notations *)
let pipe_end = End
let map f t = Map (f, t)
let iter f t = map (fun x -> f x; x) t
let op f t = map (fun x -> (fst x, f x)) t
let expand f t = Expand(f, t)

(** Eval a pipeline into the corresponding fucntion *)
let rec eval : type a b. (a, b) t -> (a, b) f =
  fun pipe x ->
    match pipe with
    (** Smple cases. *)
    | End -> x
    | Map (f, t) ->
      eval t (f x)
    (** Expand, this case is a bit tricky. Indeed, in the case where
        some inputs are *not* actually expanded, we want to avoid
        non-tailrec function calls such as fold, which explains the
        return type of the function. *)
    | Expand (f, t) ->
      match f x with
      (** The function did not actually expand the input, so we do the same as
          the Map case. *)
      | opt, `Single y ->
        eval t (opt, y)
      (** Expansion. There are two cases, either we want the result of the fold
          to be used for the rest of the evaluation, or we want to discard it.
          This is governed by the [flat] boolean (flat = true means to keep the
          return value for following evaluations). *)
      | opt, `Gen (flat, g) ->
        let aux opt c = eval t (opt, c) in
        let opt' = Gen.fold aux opt g in
        if flat then (fst x) else opt'

(** Aux function to eval a pipeline on the current value of a generator. *)
let run_aux : type a. (opt * a, opt) t -> (opt -> a option) -> opt -> opt option =
  fun pipe g opt ->
    match g opt with
    | None -> None
    | Some x ->
      Some (eval pipe (opt, x))

(** Effectively run a pipeline on all values that come from a generator.
    Time/size limits apply for the complete evaluation of each input
    (so all expanded values count toward the same limit). *)
let rec run : type a.
  ?handle_exn:(opt -> exn -> unit) ->
  (opt -> a option) -> opt -> (opt * a, opt) t -> unit =
  fun ?(handle_exn=default_handler) g opt pipe ->
    let time = opt.Options.time_limit in
    let size = opt.Options.size_limit in
    let al = setup_alarm time size in
    begin
      match run_aux pipe g opt with
      | None ->
        delete_alarm al
      | Some opt' ->
        delete_alarm al;
        run ~handle_exn g opt' pipe
      | exception exn ->
        delete_alarm al;
        if Printexc.backtrace_status () then
          Printexc.print_backtrace stdout;
        handle_exn opt exn;
        run ~handle_exn g opt pipe
    end

