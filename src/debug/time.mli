
(** Time facilities

    This module defines some time-related functions.
*)

(** {2 Types} *)

type clock = int64
(** Clock time, expressed in nanoseconds. *)

type time = float
(** Real time, rexpressed in seconds. *)

(** {2 Manipulating time} *)

val get_total_time : unit -> time
val get_total_clock : unit -> clock
(** Get the total clock/time elapsed since the beggining of the program. *)

val time_of_clock : clock -> time
val clock_of_time : time -> clock
(** Conversion between time and clock.
    WARNING: time is less precise than clock, so it is not advised to convert a
             time into a clock.
*)
