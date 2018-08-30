(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Extensions *)

val register_all : unit -> unit
(** Register all extensions. *)

val extra_hyps : unit -> Dolmen.Statement.t list
(** Some extensions may want to add some statements as preludes. *)


