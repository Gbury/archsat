
(** Pretty printing annotations

    This module defines types to specify pretty printing annotations
    (such as associtativity, infix notations, etc...).
*)


(* Pretty types *)
(* ************************************************************************ *)

type name = string

type pos =
  | Infix
  | Prefix

type assoc =
  | Left
  | Right

