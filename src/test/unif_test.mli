
(** {2 Common interface} *)

include Misc_test.S with type t := Mapping.t

(** {2 Tests} *)

val unif_tests : OUnit2.test
val unif_qtests : QCheck.Test.t list
(** Tests about unifiers. *)

val robinson_tests : OUnit2.test
val robinson_qtests : QCheck.Test.t list
(** Tests about unifiers. *)

