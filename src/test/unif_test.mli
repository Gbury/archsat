
(** {2 Common interface} *)

include Misc_test.S with type t := Unif.t

(** {2 Tests} *)

val unif_tests : OUnit2.test
(** Tests about unifiers. *)

val match_tests : OUnit2.test
(** Tests about unifiers. *)

val robinson_tests : OUnit2.test
(** Tests about unifiers. *)

