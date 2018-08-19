(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** {2 Common signatures for modules} *)

(** Standard interface for modules defining a new type. *)
module type Std = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

(** Standard interface for printing *)
module type Print = sig
  type t
  val print : Format.formatter -> t -> unit
end

(** Full interface for module defining a new type, incldues
    the standard interface, plus printing functions. *)
module type Full = sig
  include Std
  include Print with type t := t
end



(** {2 Common signatures for parametrised modules} *)

(** Variant of the standard signature for parametric types. *)
module type PolyStd = sig
  type 'a t
  val hash : 'a t -> int
  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
end

(** Standard interface for printing polymorphic types *)
module type PolyPrint = sig
  type 'a t
  val print : Format.formatter -> 'a t -> unit
end

(** Full interface for module defining a new type, incldues
    the standard interface, plus printing functions. *)
module type PolyFull = sig
  include PolyStd
  include PolyPrint with type 'a t := 'a t
end

