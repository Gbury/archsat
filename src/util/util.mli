
(** Utilities

    This module defines utilitiy functions.
*)

(** {2 Logging functions} *)

val cleanup : unit -> unit
(** Inform the logger that the current line need cleanup. *)

type 'a logger =
  ?section:Section.t ->
  ('a, Format.formatter, unit, unit) format4 ->
  'a

val error   : 'a logger
val log     : 'a logger
val warn    : 'a logger
val info    : 'a logger
val debug   : 'a logger
(** Loggers corresponding to the levels defined in {Level} *)

(** {2 Statistics} *)
module Stats : sig
  (** Statistics for debugging sections. *)

  type t
  (** The type of a statistics counter. *)

  val mk : string -> t
  (** Create a stats counter with the given name. *)

  val get : t -> Section.t -> int
  (** Get the current value of a stats counter *)

  val set : t -> Section.t -> int -> unit
  (** Set the value of a stats counter. *)

  val incr : ?k:int -> t -> Section.t -> unit
  (** Increase the value of a counter. *)

  type group
  (** A group of stats counter. Groups are used to identify
      sets of counters relevant to a set of sections.
      The idea if that not all stats counter are meaningful for
      all sections. Printing of statistics will only take into
      accounts grouped counters.
  *)

  val bundle : t list -> group
  (** Bundle a list of counters into a group. *)

  val attach : Section.t -> group -> unit
  (** Attach a section to a group of counters. *)

end

(** {2 profiling facilities} *)

val enter_prof : Section.t -> unit
val exit_prof : Section.t -> unit
(** Enter & Exit the profiler *)

val csv_prof_data : Format.formatter -> unit
(** Print profiling data in csv format for re-use by other programs. *)

val enable_profiling : unit -> unit
(** Enable printing of profiling info at exit (disabled by default) *)

val enable_statistics : unit -> unit
(** Enable printing of statistices at exit (disabled by default) *)

