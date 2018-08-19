(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Utilities

    This module defines utilitiy functions.
*)

(** {2 Size functions} *)

val size : 'a -> float
(** Reutnrs the size of the transitive closure of the given object, in bytes *)

val print_size : Format.formatter -> float -> unit
(** Print a siez (in bytes), using a human readble format *)


(** {2 Logging functions} *)

val printf : ('a, Format.formatter, unit) format -> 'a
(** Print the given format string on the program output *)

val cleanup : unit -> unit
(** Inform the logger that the current line need cleanup. *)

val enable_debug : unit -> unit
(** Enable debug mode. *)

val disable_time : unit -> unit
(** Disable time printing in logs (useful to compare logs). *)

type 'a logger =
  ?section:Section.t -> ('a, Format.formatter, unit, unit) format4 -> 'a
(** Th type of a logger. *)

val log     : 'a logger
val error   : 'a logger
val warn    : 'a logger
val info    : 'a logger
val debug   : 'a logger
(** Loggers corresponding to the levels defined in {Level} *)

(** {2 profiling facilities} *)

val enter_prof : Section.t -> unit
val exit_prof : Section.t -> unit
(** Enter & Exit the profiler *)

val within_prof : Section.t -> ('a -> 'b) -> 'a -> 'b
(** Computes the given function inside the profiler for the given section.
    The given function can raise an exception safely. *)

val clean_exit : unit -> unit
(** Properly closes evrything that might have not be closed.
    Cuerrently closes all still active profiling section upon exit. *)
