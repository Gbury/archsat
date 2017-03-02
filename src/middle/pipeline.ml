
(* Default functions *)
(* ************************************************************************ *)

let default_finally opt = opt

let default_handler opt fmt exn =
  Format.fprintf fmt "Exception: @<hov>%s@]@." (Printexc.to_string exn)

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
        Util.cleanup ();
        raise Options.Out_of_time)
  )

(* We also want to catch user interruptions *)
let () =
  Sys.set_signal Sys.sigint (
    Sys.Signal_handle (fun _ ->
        Util.cleanup ();
        raise Options.Sigint)
  )

(* Pipeline and execution *)
(* ************************************************************************ *)

(** Some aliases for readibility *)
type opt = Options.opts

type 'a gen = 'a Gen.t
type 'a fix = [ `Ok | `Gen of bool * 'a gen ]

type ('a, 'b) op = {
  name : string;
  f : 'a -> 'b;
}

(** Type for pipelines, i.e a series of transformations to
    apply to the input. An ('a, 'b) t is a pipeline that
    takes an input of type ['a] and returns a value of type
    ['b]. *)
type (_, _) t =
  (** The end of the pipeline, the identity/reflexive constructor *)
  | End :
      ('a, 'a) t
  (** Apply a single function and then proceed with the rest of the pipeline *)
  | Map :
      ('a, 'c) op * ('c, 'b) t -> ('a, 'b) t
  (** Concat two pipeline. Not tail recursive. *)
  | Concat :
      ('a, 'b) t * ('b, 'c) t -> ('a, 'c) t
  (** Fixpoint expansion *)
  | Fix :
      ('opt * 'a, 'opt * 'a fix) op * ('opt * 'a, 'opt) t -> ('opt * 'a, 'opt) t

(** Creating pipelines. *)

let apply ?(name="") f =
  { name; f; }
let f_map ?(name="") f =
  { name; f = (fun ((opt, y) as x) -> opt, f x); }
let iter_ ?(name="") f =
  { name; f = (fun x -> f x; x); }

let _end = End
let (@>>>) op t = Map(op, t)
let (@|||) t t' = Concat (t, t')

let fix op t = Fix(op, t)

(** Eval a pipeline into the corresponding function *)
let rec eval : type a b. (a, b) t -> a -> b =
  fun pipe x ->
    match pipe with
    | End -> x
    | Map (op, t) ->
      eval t (op.f x)
    | Concat (t, t') ->
      let y = eval t x in
      eval t' y
    | Fix (op, t) ->
      let opt, y = x in
      begin match op.f x with
        | opt', `Ok -> eval t (opt', y)
        | opt', `Gen (flat, g) ->
          let aux opt c = eval pipe (opt, c) in
          let opt'' = Gen.fold aux opt' g in
          if flat then opt'' else opt
      end

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
let rec run :
  type a.
  ?finally:(opt -> opt) ->
  ?print_exn:(opt -> Format.formatter -> exn -> unit) ->
  (opt -> a option) -> opt -> (opt * a, opt) t -> unit
  =
  fun
    ?(finally=default_finally)
    ?(print_exn=default_handler)
    g opt pipe ->
    let time = opt.Options.time_limit in
    let size = opt.Options.size_limit in
    let al = setup_alarm time size in
    begin
      match run_aux pipe g opt with
      | None -> delete_alarm al
      | Some opt' ->
        delete_alarm al;
        let opt'' = try finally opt' with _ -> opt' in
        run ~finally ~print_exn g opt'' pipe
      | exception exn ->
        delete_alarm al;
        if Printexc.backtrace_status () then
          Printexc.print_backtrace stdout;
        Util.error "%a" (print_exn opt) exn;
        let opt' = try finally opt with _ -> opt in
        run ~finally ~print_exn g opt' pipe
    end

