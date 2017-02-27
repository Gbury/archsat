
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


(** {2 Inspection} *)

val full_name : t -> string
(** Full path to the section. *)

val short_name : t -> string
(** Short name of the section. *)


(** {2 Logging} *)

val set_debug : t -> Level.t -> unit
(** Debug level for section (and its descendants) *)

val clear_debug : t -> unit
(** Clear debug level (will be same as parent's) *)

val get_debug : t -> Level.t option
(** Specific level of this section, if any *)

val cur_level : t -> int
(** Current debug level, with parent inheritance *)


(** {2 Profiling} *)

val profile_section : t -> unit
(** Activate profiling for a section and all its children (overrides max depth) *)

val set_profile_depth : int -> unit
(** Set maximum depth for profiling *)


(** {2 Access} *)

(** TODO: change these functions ? *)

val find : string -> t

val iter : ((string * t) -> unit) -> unit


