
(** Export facilities

    This module defines wrappers around functions that
    export problems in various format such as tptp.
*)

(** {2 Main functions} *)

val init : Options.opts -> unit -> unit

val declare_id :
  ?loc:Dolmen.ParseLocation.t -> Options.opts ->
  Term.id list -> (Dolmen.Id.t * Term.id) -> unit

val declare_hyp :
  ?loc:Dolmen.ParseLocation.t -> Options.opts ->
  Term.id list -> Term.id -> unit

val declare_goal :
  ?loc:Dolmen.ParseLocation.t -> Options.opts ->
  Term.id list -> Term.id -> unit

val declare_solve :
  ?loc:Dolmen.ParseLocation.t -> Options.opts -> unit -> unit
