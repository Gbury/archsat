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

  val full_name : t -> string  (** Full path to the section *)
  val short_name : t -> string

  val set_debug : t -> int -> unit (** Debug level for section (and its descendants) *)
  val clear_debug : t -> unit (** Clear debug level (will be same as parent's) *)
  val get_debug : t -> int option (** Specific level of this section, if any *)
  val cur_level : t -> int (** Current debug level, with parent inheritance *)

  val find : string -> t
  val iter : ((string * t) -> unit) -> unit

  val root : t (** Default section, with no parent *)

  val make : ?parent:t -> ?inheriting:t list -> ?stats:int array -> string -> t
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

  val stats : t -> int array
  (** Return the stat array (of length determinadby the section creation) *)

  val set_stats :t -> int array -> unit
  (** Allows to set the array to be used to record statistics *)

end

val incr : ?k:int -> Section.t -> int -> unit
(** [incr ?k section i] increases the i-th cell of stats of [section] by [k] (default [k=1]). *)

val set_debug : int -> unit     (** Set debug level of [Section.root] *)
val get_debug : unit -> int     (** Current debug level for [Section.root] *)
val need_cleanup : bool ref     (** Cleanup line before printing? *)

val debug : ?section:Section.t -> int ->
  ('a, Buffer.t, unit, unit) format4 -> 'a
(** Print a debug message, with the given section and verbosity level.
    The message might be dropped if its level is too high.
    {b NOTE}: non-thread safe *)

(** {2 profiling facilities} *)

val enable_profiling : unit -> unit   (** Enable profiling (disabled by default) *)

val enter_prof : Section.t -> unit                (** Enter the profiler *)
val exit_prof : Section.t -> unit                 (** Exit the profiler *)

val csv_prof_data : Format.formatter -> unit

(** {2 LogtkOrdering utils} *)

val lexicograph : ('a -> 'b -> int) -> 'a list -> 'b list -> int
(** lexicographic order on lists l1,l2 which elements are ordered by f *)

(** {2 List misc} *)

val list_iteri2 : (int -> 'a -> 'b -> unit) -> 'a list -> 'b list -> unit
(** Same as List.iteri but on 2 lists at the same time.
    @raise Invalid_argument "list_iteri2" if lists have different lengths *)

