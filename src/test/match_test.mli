
(** {2 Common interface} *)

include Misc_test.S with type t := Mapping.t

(** {2 Tests} *)

val match_tests : OUnit2.test
val match_qtests : QCheck.Test.t list
(** Tests about unifiers. *)


