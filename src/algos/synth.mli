(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Term synhtesis

    This module sprovides facilities to generate a term given a type,
    using the defined functions symbols. Used mainly to replace meta-variables
    with a ground term of the correct type
*)


(** {2 Synhtetizing} *)

val add_id : Expr.Id.Const.t -> unit
(** Add the given function symbol to the set of known symbols. *)

val register : Expr.term -> unit
(** Register the type as the representant of its type when
    synhtetising terms. *)

val ty : Expr.ty
(** A type to replace type metas with. Will be compatible with
    synthetized terms. *)

val term : Expr.ty -> Expr.term
(** Tries and generated a term of the given type.
    @raise Not_found if couldn't synthetize a term. *)

