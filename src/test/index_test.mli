(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

val correct_tests : OUnit2.test
val correct_qtests : QCheck.Test.t list
(** Serie of tests to verify the soundeness of the various indexes. *)

val complete_tests : OUnit2.test
val complete_qtests : QCheck.Test.t list
(** Serie of tests to verify the soundeness of the various indexes. *)

