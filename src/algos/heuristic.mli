(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Heuristics about unifiers.
    This module implements heuristics to give scores to instantiations
    based on the status of expressions. Highly experimental. *)

val goal_directed : Mapping.t -> int
(** Gives higher scores to substitutions in wich terms are mapped
    to expressions coming from goals. *)

