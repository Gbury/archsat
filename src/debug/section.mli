
(** Sections

    This module defines sections. Sections are used for logging, profiling,
    and statistics.
*)

(** {2 Basics} *)

type t
(** The type for debugging sections *)

val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
(** Usual functions. *)

val root : t
(** Default section, with no parent *)

val make : ?parent:t -> ?inheriting:t list -> string -> t
(** [make ?parent ?inheriting name] makes a new section with the given name.
    It has a parent (default [root]), used to give it a name. It can
    also have a list of sections it inherits from. *)


(** {2 Section names} *)

val find : string -> t
(** Find a section by its full name *)

val iter : (t -> unit) -> unit
(** Iter over all sections. *)

val full_name : t -> string
(** Full path to the section. *)

val short_name : t -> string
(** Short name of the section. *)


(** {2 Logging} *)

val clear_debug : t -> unit
(** Clear debug level (will be same as parent's) *)

val get_debug : t -> Level.t option
(** Specific level of this section, if any *)

val set_debug : t -> Level.t -> unit
(** Debug level for section (and its descendants) *)

val cur_level : t -> Level.t
(** Current debug level, with parent inheritance *)


(** {2 Profiling} *)

val curr : unit -> t option
(** Returns the currently profiled section. *)

val enter : t -> unit
val exit  : t -> unit
(** Enter and exit a section for profiling. *)

val profile_section : t -> unit
(** Activate profiling for a section and all its children (overrides max depth) *)

val set_profile_depth : int -> unit
(** Set maximum depth for profiling *)

val print_profiling_info : unit -> unit
(** Print profiling info *)

(** {2 Statistics access} *)

val max_stats : int
(** The maximum number of stats that can be recorded, i.e the size
    of the array returned by the {stats} funciton. *)

val stats : t -> int array
(** Statistics aray. Should only be directly accessed in module {Stats}. *)

