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

(** {2 Debugging} *)

(** Debug section *)
module Section : sig
  type t

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual functions. *)

  val full_name : t -> string  (** Full path to the section *)
  val short_name : t -> string

  val set_debug : t -> int -> unit (** Debug level for section (and its descendants) *)
  val clear_debug : t -> unit (** Clear debug level (will be same as parent's) *)
  val get_debug : t -> int option (** Specific level of this section, if any *)
  val cur_level : t -> int (** Current debug level, with parent inheritance *)

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

val set_debug : int -> unit     (** Set debug level of [Section.root] *)
val get_debug : unit -> int     (** Current debug level for [Section.root] *)
val need_cleanup : bool ref     (** Cleanup line before printing? *)

val log :
  ?section:Section.t -> int ->
  ('a, Format.formatter, unit, unit) format4 ->
  ('a -> unit) -> unit
(** Print a debug message, with the given section and verbosity level.
    The message might be dropped if its level is too high. *)

(** {2 Statistics} *)
module Stats : sig
  type t

  val mk : string -> t

  val get : t -> Section.t -> int
  val set : t -> Section.t -> int -> unit
  val incr : ?k:int -> t -> Section.t -> unit

  type group
  val bundle : t list -> group
  val attach : Section.t -> group -> unit
end

(** {2 profiling facilities} *)

val enter_prof : Section.t -> unit                (** Enter the profiler *)
val exit_prof : Section.t -> unit                 (** Exit the profiler *)

val csv_prof_data : Format.formatter -> unit

val enable_profiling : unit -> unit   (** Enable printing of profiling info (disabled by default) *)
val enable_statistics : unit -> unit  (** Enable printing of statistices (disabled by default) *)

