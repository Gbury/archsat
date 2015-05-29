
val register :
  ?descr:string ->
  ?priority:int ->
  ?tptp_builtins:Type.builtin_symbols ->
  ?smtlib_builtins:Type.builtin_symbols ->
  ?propagate_assert:(string -> Expr.formula -> bool) ->
  string -> unit

val set_ext : string -> unit
val set_exts : string -> unit

val log_active : unit -> unit

val type_env : Options.input -> Type.builtin_symbols

