(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Statistics

    This module defines functiosn to register statistics about sections.
*)

val print : unit -> unit
(** Print statistics on the standard output. *)

(* {2 Statistics counters} *)

type t
(** The type of a statistics counter. *)

exception Out_of_stats
(** Raised when trying to create a statistics but there are already
    Debug.max_stats that have been created. *)

val mk : string -> t
(** Create a stats counter with the given name.
    @raise Out_of_stats if cannot create stats anymore. *)

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

val add_to_group : group -> t -> unit
(** Add a statistics to a group. *)

val attach : Section.t -> group -> unit
(** Attach a section to a group of counters. *)

