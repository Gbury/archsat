(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Extension for polymorphic functional arrays *)

val hyps : unit -> Dolmen.Statement.t list
(** Add extra hypotheses (for the axiom mode) *)

val register : unit -> unit
(** Register the extension *)

