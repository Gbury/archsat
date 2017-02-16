
(** {2 Common signatures for modules} *)

(** Standard interface for modules defining a new type. *)
module type S = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

(** Full interface for module defining a new type, incldues
    the standard interface, plus printing functions. *)
module type Full = sig
  include S
  val debug : Buffer.t -> t -> unit
  val print : Format.formatter -> t -> unit
end

(** Variant of the standard signature for parametric types. *)
module type Poly = sig
  type 'a t
  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
end

(** Variant of the full interface for parametric types. *)
module type PolyFull = sig
  include Poly
  val debug : Buffer.t -> 'a t -> unit
  val print : Format.formatter -> 'a t -> unit
end
