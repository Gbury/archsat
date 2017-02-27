(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 Some helpers} *)

(** {2 Time facilities} *)

(** time elapsed since start of program *)
val get_total_time : unit -> float

(** {2 Debugging modules} *)

module Level : sig
  (** Debugging levels *)

  type t
  (** The type of logging levels *)

  val error : t
  (** Level for errors. Errors are always printed. *)

  val log : t
  (** Level for general logging. General logging messages
      are printed by default. *)

  val warn : t
  (** Level for warnings. *)

  val info : t
  (** Level for information messages. *)

  val debug : t
  (** Level for debugging messages. *)

  val max : t -> t -> t
  (** Compute the max of two debug levels *)

end

module Section : sig
  (** Debugging sections *)

  type t

  val full_name : t -> string
  (** Full path to the section. *)

  val short_name : t -> string
  (** Short name of the section. *)

  val set_debug : t -> Level.t -> unit
  (** Debug level for section (and its descendants) *)

  val clear_debug : t -> unit
  (** Clear debug level (will be same as parent's) *)

  val get_debug : t -> Level.t option
  (** Specific level of this section, if any *)

  val cur_level : t -> int
  (** Current debug level, with parent inheritance *)

  val find : string -> t
  val iter : ((string * t) -> unit) -> unit

  val root : t (** Default section, with no parent *)

  val make : ?parent:t -> ?inheriting:t list -> string -> t
  (** [make ?parent ?inheriting name] makes a new section with the given name.
      It has a parent (default [root]), used to give it a name. It can
      also have a list of sections it inherits from.
      Unless specificed explicitely otherwise (using
      {!set_debug}) the level of the section will be the max level of its
      parent and its inherited sections. *)

  val profile_section : t -> unit
  (** Activate profiling for a section and all its children (overrides max depth) *)

  val set_profile_depth : int -> unit
  (** Set maximum depth for profiling *)
end

(** {2 Logging functions} *)

val set_debug : Level.t -> unit
(** Set debug level of [Section.root] *)

val get_debug : unit -> Level.t
(** Current debug level for [Section.root] *)

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

