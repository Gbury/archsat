
(** Logging levels

    This module defines logging levels.
*)

(** {2 Level type} *)

type t
(** The type of logging levels *)

val equal : t -> t -> bool
(** Equality function on levels. *)

val compare : t -> t -> int
(** Comparison functions on levels *)

val max : t -> t -> t
(** Compute the max of two debug levels *)

val prefix : Format.formatter -> t -> unit
(** Return a color for printing messages of this level *)

val to_string : t -> string
(** Convert a level to a string. *)


(** {2 Existing levels} *)

val null : t
(** Null level. Shouldn't be used. *)

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


