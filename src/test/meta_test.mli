(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** {2 Common interface} *)

val state : Ext_meta.state QCheck.arbitrary
(** Generator for meta unification state. *)

(** {2 Tests} *)

val meta_qtests : QCheck.Test.t list
(** Tests related to full state meta unification *)

