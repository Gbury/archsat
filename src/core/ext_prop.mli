(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Extension for two-value logic

    This extension aims to bridge assignments and
    SAT solver propagations/decisions for predicates. *)

val register : unit -> unit
(** Register the extension. *)

