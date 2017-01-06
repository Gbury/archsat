
(** Random Expressions

    This module defines some random generators for expressions.
    These are intended for use in qcheck tests.
*)

(** {2 Constants} *)

module C : sig

  val type_a : Expr.ty
  val type_b : Expr.ty
  val type_prop : Expr.ty
  (** Base types used in the generation of terms. *)

  val mk_list_type : Expr.ty -> Expr.ty
  val mk_pair_type : Expr.ty -> Expr.ty -> Expr.ty
  (** Composite types used in the generation of terms. *)

  val a_0 : Expr.ty Expr.function_descr Expr.id
  val a_1 : Expr.ty Expr.function_descr Expr.id
  val a_2 : Expr.ty Expr.function_descr Expr.id
  val f_a : Expr.ty Expr.function_descr Expr.id
  val g_a : Expr.ty Expr.function_descr Expr.id
  val h_a : Expr.ty Expr.function_descr Expr.id
  val b_0 : Expr.ty Expr.function_descr Expr.id
  val b_1 : Expr.ty Expr.function_descr Expr.id
  val b_2 : Expr.ty Expr.function_descr Expr.id
  val f_b : Expr.ty Expr.function_descr Expr.id
  val g_b : Expr.ty Expr.function_descr Expr.id
  val h_b : Expr.ty Expr.function_descr Expr.id
  val p_0 : Expr.ty Expr.function_descr Expr.id
  val p_1 : Expr.ty Expr.function_descr Expr.id
  val p_2 : Expr.ty Expr.function_descr Expr.id
  val f_p : Expr.ty Expr.function_descr Expr.id
  val g_p : Expr.ty Expr.function_descr Expr.id
  val h_p : Expr.ty Expr.function_descr Expr.id
  val pair : Expr.ty Expr.function_descr Expr.id
  val nil : Expr.ty Expr.function_descr Expr.id
  val cons : Expr.ty Expr.function_descr Expr.id
  (** Constants used in the generation of terms. *)

end

(** {2 Variables} *)

module Var : sig

  val get : Expr.ty -> Expr.ty Expr.id array
  (** Return an array of variables of the given type. *)

  val gen : Expr.ty -> Expr.ty Expr.id QCheck.Gen.t
  (** Generate a variable of the given type. *)

end

(** {2 Meta-variables} *)

module Meta : sig

  val get : Expr.ty -> Expr.ty Expr.meta array
  (** Return an array of meta-variables of the given type. *)

  val gen : Expr.ty -> Expr.ty Expr.meta QCheck.Gen.t
  (** Generate a variable of the given type. *)

end

(** {2 Types} *)

module Ty : sig

  include Misc_test.S with type t := Expr.ty

end

(** {2 Terms} *)

module Term : sig

  include Misc_test.S with type t := Expr.term

  type config = {
    var : int;
    meta: int;
  }

  val typed : config:config -> Expr.ty -> Expr.term QCheck.Gen.sized
  (** Generate a term with the given size and type.
      @param ground if false then variables can appear in the generatd term.
        (default [true]) *)

end

(** {2 Formulas} *)

module Formula : sig

  include Misc_test.S with type t := Expr.formula

  type config = {
    term  : Term.config;
    eq    : int;
    pred  : int;
    neg   : int;
    conj  : int;
    disj  : int;
    impl  : int;
    equiv : int;
    all   : int;
    allty : int;
    ex    : int;
    exty  : int;
  }

  val eq : config:config -> Expr.formula QCheck.Gen.sized
  val pred : config:config -> Expr.formula QCheck.Gen.sized
  (** Individual generator for expressions. *)

  val guided : config:config -> Expr.formula QCheck.Gen.sized
  (** Generate a formula using a given configuration. *)

  val closed : config:config -> Expr.formula QCheck.Gen.sized
  (** Generate a closed formula. *)

  val meta : Expr.formula -> Expr.formula
  (** Replaces variable with meta-variables in the formulas of a generator. *)

  val meta_tt : (Expr.term * Expr.term) -> (Expr.term * Expr.term)
  (** Takes a pair of terms with free variables and substitute them with
      meta-variables. *)

end

