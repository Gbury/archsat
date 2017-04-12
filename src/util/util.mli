
(** Utilities

    This module defines utilitiy functions.
*)

(** {2 Output functions} *)

val printf : ('a, Format.formatter, unit) format -> 'a
(** Print the given format string on the program output *)

(** {2 Logging functions} *)

val cleanup : unit -> unit
(** Inform the logger that the current line need cleanup. *)

val enable_debug : unit -> unit
(** Enable debug mode. *)

val disable_time : unit -> unit
(** Disable time printing in logs (useful to compare logs). *)

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 ->
  'a
(** Th type of a logger. *)

val error   : 'a logger
val log     : 'a logger
val warn    : 'a logger
val info    : 'a logger
val debug   : 'a logger
(** Loggers corresponding to the levels defined in {Level} *)

(** {2 profiling facilities} *)

val enter_prof : Section.t -> unit
val exit_prof : Section.t -> unit
(** Enter & Exit the profiler *)

val clean_exit : unit -> unit
(** Properly closes evrything that might have not be closed.
    Cuerrently closes all still active profiling section upon exit. *)
