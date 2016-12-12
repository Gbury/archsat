
type ext

val mk_ext :
  ?tptp:Type.builtin_symbols ->
  ?smtlib:Type.builtin_symbols ->
  ?zf:Type.builtin_symbols ->
  unit -> ext

val type_env : In.language -> Type.builtin_symbols

module Addon : Extension.S with type ext = ext

