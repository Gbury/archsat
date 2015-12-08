
val current_round : unit -> int
(** Returns the index of the current round. *)

val inst_done : unit -> unit
(** Adds one to the number of instanciatiosn done on the current round. *)

val inst_remaining : int -> unit
(** Sets the number of instanciations remaining to do this round. *)



