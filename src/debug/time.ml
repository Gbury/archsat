
(* types *)
(* ************************************************************************ *)

type clock = int64
(* Clock time, in nanoseconds. *)

type time = float
(* Real time, in seconds. *)

(* Conversions *)
(* ************************************************************************ *)

let time_of_clock c =
  (Int64.to_float c) /. (10. ** 9.)

let clock_of_time t =
  Int64.of_float (t *. (10. ** 9.))

(* Time facilities *)
(* ************************************************************************ *)

let ckid = match Oclock.process_cputime with
  | Some c -> c
  | None -> Oclock.realtime

let get_total_clock =
  let start = Oclock.gettime ckid in
  (fun () ->
     let stop = Oclock.gettime ckid in
     Int64.sub stop start
  )

let get_total_time () = time_of_clock (get_total_clock ())

