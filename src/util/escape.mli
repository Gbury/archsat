
(** Escpaing identifiers

    This module provides helpers to print identifers
    in languages that restricts the range of acceptable characters
    (for instance HTML, Coq, ...) *)


(** {2 Wrapper aroun polymorphic identifiers} *)

module Any : sig

  type t = Id : _ Expr.id -> t
  val hash : t -> int
  val equal : t -> t -> bool

end

(** {2 Environment for escaping} *)

type t
(** The type of environnment/escaper for a given language. *)

val print : t -> Format.formatter -> _ Expr.id -> unit
(** Printer for identifiers using a given environment, and record its actual
    printed string, in order to avoid future conflicts with other escaped
    identifiers. *)

val print_string : t -> Format.formatter -> string -> unit
(** Print a given string and escape it, but do not record it. *)

(** Custom environments *)

val mk :
  lang:string ->
  name:(Any.t -> string) ->
  escape:(string -> string) ->
  rename:(string -> string) -> t
(** Create an escaper from scratch. The name function is called to determine
    the name of an identifier. The escape function is assumed
    to be idempotent and have a lot of fixpoints (i.e. all valid identifiers
    name should map to themselves) whereas the renaming function should
    have absolutely no fixpoint (i.e. for all strings [rename s <> s]) *)

val rename : sep:char -> string -> string
(** A renaming function, which add an increasing number after the given separator. *)

val umap :
  (int -> Uchar.t option -> Uchar.t list) ->
  string -> string
(** [umap f] provides an equivalent of flat_map on unicode strings.
    [f] is given the position of the character in the string (starting from [1]),
    and a unicode character (or [None] is decoding failed for that byte). *)
