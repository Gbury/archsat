
(** {2 Common interface} *)

include Misc_test.S with type t := Mapping.t

val pair : (Expr.term * Expr.term) QCheck.arbitrary
(** Arbitrary for pairs of terms with the same type. *)

val pair_sized : int QCheck.Gen.t -> (Expr.term * Expr.term) QCheck.arbitrary
(** Arbitrary for pairs of terms with the same type. *)

(** {2 Tests} *)

val unif_tests : OUnit2.test
val unif_qtests : QCheck.Test.t list
(** Tests about unifiers. *)

val robinson_tests : OUnit2.test
val robinson_qtests : QCheck.Test.t list
(** Tests about unifiers. *)

