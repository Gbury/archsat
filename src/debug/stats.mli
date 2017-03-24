
(** Statistics

    This module defines functiosn to register statistics about sections.
*)

(* {2 Statistics counters} *)

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

(** {2 Statistics groups} *)

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

val print : unit -> unit
(** Print statistics on the standard output. *)

