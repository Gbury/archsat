
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
    argument of an application, and then following the path [t]. *)

val path : int list -> t
(** [path l] if [List.fold_right arg l root]. *)

(** {2 Position results} *)

type 'a res =
  | Var                                   (** A variable *)
  | Top of 'a Expr.function_descr Expr.id (** An application of a function symbol. *)
  | Possible                              (** The path goes through a variable. *)
  | Impossible                            (** The path cannot occur. *)
(** This type represents what can occur at the end of a path. *)

val print_res : (Format.formatter -> 'a Expr.function_descr Expr.id -> unit) ->
                Format.formatter -> 'a res -> unit
(** Print a res. *)

(** {2 Apply positions to types} *)

module Ty : sig
  val apply : t -> Expr.ty -> Expr.ttype res * Expr.ty option
  val substitute : t -> by:Expr.ty -> Expr.ty -> Expr.ty option
  val fold : ('a -> t -> Expr.ty -> 'a) -> 'a -> Expr.ty -> 'a
  val find_map : (t -> Expr.ty -> 'a option) -> Expr.ty -> 'a option
end

(** {2 Apply positions to terms} *)

module Term : sig
  val apply : t -> Expr.term -> Expr.ty res * Expr.term option
  val substitute : t -> by:Expr.term -> Expr.term -> Expr.term option
  val fold : ('a -> t -> Expr.term -> 'a) -> 'a -> Expr.term -> 'a
  val find_map : (t -> Expr.term -> 'a option) -> Expr.term -> 'a option
end



