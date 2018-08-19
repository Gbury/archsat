(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** {2 Positions} *)

type t
(** The type of positions. *)

val equal : t -> t -> bool
(** Equality on positions. *)

val compare : t -> t -> int
(** Compare two positions. *)

val print : Format.formatter -> t -> unit
(** Print positions. *)

val root : t
(** The root position. *)

val arg : int -> t -> t
(** [arg i t] returns the position obtained by inspecting the [i]-th
    argument of an application, and then following the path [t].
    Argument numbering starts at 0, i.e. the same as for arrays
    @raise Invalid_argument if [i < 0]
*)

val follow : t -> int -> t
(** Follow the given path [t] then take the [i]-th argument *)

val path : int list -> t
(** [path l] is [List.fold_right arg l root]. *)

val concat : t -> t -> t
(** Concat two paths *)

(** {2 Position results} *)

type ('a, 'b) res =
  | Var                                         (** A variable *)
  | Top of ('a, 'b) Expr.function_descr Expr.id (** An application of a function symbol. *)
  | Possible                                    (** The path goes through a variable. *)
  | Impossible                                  (** The path cannot occur. *)
(** This type represents what can occur at the end of a path. *)

val print_res :
  (Format.formatter -> ('a, 'b) Expr.function_descr Expr.id -> unit) ->
  Format.formatter -> ('a, 'b) res -> unit
(** Print a res. *)


(** {2 Apply positions to proof terms} *)

module Proof : sig
  val apply : t -> Term.t -> Term.t option
  val substitute : t -> by:Term.t -> Term.t -> Term.t option
  val find : Term.t -> Term.t -> t option
end

(** {2 Apply positions to types} *)

module Ty : sig
  val apply : t -> Expr.ty -> (unit, Expr.ttype) res * Expr.ty option
  val substitute : t -> by:Expr.ty -> Expr.ty -> Expr.ty option
  val fold : ('a -> t -> Expr.ty -> 'a) -> 'a -> Expr.ty -> 'a
  val find_map : (t -> Expr.ty -> 'a option) -> Expr.ty -> 'a option
end

(** {2 Apply positions to terms} *)

module Term : sig
  val apply : t -> Expr.term -> (Expr.ttype, Expr.ty) res * Expr.term option
  val substitute : t -> by:Expr.term -> Expr.term -> Expr.term option
  val fold : ('a -> t -> Expr.term -> 'a) -> 'a -> Expr.term -> 'a
  val find_map : (t -> Expr.term -> 'a option) -> Expr.term -> 'a option
end

