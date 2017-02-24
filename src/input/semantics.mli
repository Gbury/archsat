
(** {2 Semantic extensions} *)

type ext
(** The type of a semantic extension. *)

module Addon : Extension.S with type ext = ext
(** Module for registering addons *)

val section : Util.Section.t
(** Section for semantics extensions. *)

val type_env : In.language -> Type.builtin_symbols
(** Access to the current semantic typing function. *)

val mk_ext :
  ?tptp:Type.builtin_symbols ->
  ?smtlib:Type.builtin_symbols ->
  ?zf:Type.builtin_symbols ->
  unit -> ext
(** Create a semantic extension. *)

