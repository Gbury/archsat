
type ext

module Addon : Extension.S with type ext = ext

val mk_ext :
  ?tptp:Type.builtin_symbols ->
  ?smtlib:Type.builtin_symbols -> unit -> ext

val type_env : Options.input -> Type.builtin_symbols

