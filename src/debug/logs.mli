
(** Debug module

    This module defines the debug mode functions
*)

(** {2 Logging} *)

val add : section:Section.t -> lvl:Level.t -> string -> unit
(** Add a new logged message. *)

val log :
  section:Section.t -> lvl:Level.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
(** Add a new logged message, using a formatter string. *)


(** {2 Log access} *)

type t = private {
  time    : int64;
  section : Section.t;
  lvl     : Level.t;
  msg     : string;
}
(** The type of a logged message. *)

val length : unit -> int
(** The current number of recorded messages *)

val get : int -> t
(** Get the n-th logged message. *)

