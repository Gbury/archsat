(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** {2 Helper functions} *)

type 'a iter = ('a -> unit) -> unit
(** Type of sequences, see the Iter library.
    TODO: insert link for Iter. *)

val iter_filter : ('a -> bool) -> 'a iter -> 'a iter
(** Filter a sequence. *)

val split : int -> int -> int list QCheck.Gen.t
(** [split n len] splits n into a list of length [len] where
    the sum of all elements is equal to [n]. *)

val split_int : int -> (int * int) QCheck.Gen.t
(** [split n] splits an integer into two itnegers whose sum
    is [n]. *)

val sublist : 'a list -> 'a list QCheck.Gen.t
(** [sublist l] returns a generator that returns a list whose elements
    belong to [l] (order is not preserved). *)

(** {2 Some module aliases} *)

module Infix : sig

  module G = QCheck.Gen
  module I = QCheck.Iter
  module S = QCheck.Shrink

end

(** {2 Common interface for value generation} *)

module type S = sig

  type t

  val print : t -> string
  (** Print types to string. *)

  val small : t -> int
  (** Returns the size of a type. *)

  val shrink : t QCheck.Shrink.t
  (** Shrink a type by trying all its subtypes. *)

  val sized : t QCheck.Gen.sized
  (** A sized generator for types. *)

  val gen : t QCheck.Gen.t
  (** Generate a random type. *)

  val t : t QCheck.arbitrary
  (** Arbitrary for types. To use in qcheck tests. *)

  val make : t QCheck.Gen.t -> t QCheck.arbitrary
  (** Convenient shortcut. *)

end

