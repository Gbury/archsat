
exception Abort of string * string
exception Extension_not_found of string * string * string list

module type K = sig
  type t

  val dummy : t
  val merge : t list -> t

  val section : Util.Section.t
end

module type S = Extension_intf.S

module Make(E: K) : S with type ext = E.t

