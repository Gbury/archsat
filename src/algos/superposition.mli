
(** Unification between terms using unitary supperposisiton.
    This module uses unitary supperposition to derive potential unifiers. *)

(** {2 Superposition configuration} *)

type rules = {
  er : bool; es : bool;
  sn : bool; sp : bool;
  rn : bool; rp : bool;
  mn : bool; mp : bool;
}
(** The type of configuration for superposition.
    Each bool indicates wether the corresponding rule should be used. *)

val mk_rules :
  default:bool ->
  ?er:bool -> ?es:bool ->
  ?sn:bool -> ?sp:bool ->
  ?rn:bool -> ?rp:bool ->
  ?mn:bool -> ?mp:bool ->
  unit -> rules
(** Convenience function to create a set of rules. *)


(** {2 Superposistion} *)

type t
(** Persistent type for supperposisiton. *)

val empty :
  ?max_depth:int -> ?rules:rules ->
  ?callback:((Expr.formula * Mapping.t) list -> Mapping.t list -> unit) ->
  Section.t -> t
(** Create an empty supperposisiton state. The callback function provided
    will be called on all pairs of (rewrites and unifiers) found during
    solving.
    @param rules Specify what rules to use during saturation.
      By default all rules are used.
*)

val add_eq : t -> ?f:Expr.formula -> Expr.term -> Expr.term -> t
val add_neq : t -> ?f:Expr.formula -> Expr.term -> Expr.term -> t
(** Add an (in)equality to the state queue, i.e it does not do much. *)

val solve : t -> t
(** Solve the given system, saturating the state with the inferred
    equalities and inequalities. It is during this function call that
    the callback given when creating the state is called. *)

