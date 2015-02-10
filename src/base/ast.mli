
(** {2 Untyped expressions} *)

type location = ParseLocation.t

type symbol =
  | Int of string
  | Rat of string
  | Real of string
  | Hexa of string
  | Binary of string
  | String of string
  | Ttype | Wildcard
  | True | False
  | Eq | Distinct | Ite | Arrow
  | All | AllTy | Ex | Let
  | And | Or | Xor
  | Imply | Equiv | Not

type term_descr =
  | Var of string
  | Column of term * term
  | Const of symbol
  | App of term * term list
  | Binding of symbol * term list * term

and term = {
  loc : location option;
  term : term_descr;
}

(** {2 Commands} *)

type command =
  | Sat of Expr.Formula.t list list         (** Special case for dimacs input *)
  | Push                                    (** Push *)
  | Pop                                     (** Pop *)
  | NewType of string * symbol * int        (** New type constructor *)
  | TypeDef of string * symbol * term       (** Type definition *)
  | TypeAlias of symbol * term list * term  (** Type alias (smtlib style) *)
  | Alias of symbol * term list * term      (** Alias (smtlib style) *)
  | Assert of string * term                 (** Add term to the assertions *)
  | CheckSat                                (** Check-sat *)
  | Unknown                                 (** For non-implemented smtlib commands *)

(** {2 Printing} *)

val debug_symbol : Buffer.t -> symbol -> unit
val debug_term : Buffer.t -> term -> unit

val print_command_name : Format.formatter -> command -> unit

(** {2 Symbols} *)
val wildcard : symbol
val distinct : symbol
val sym : string -> symbol

val int : string -> symbol
val rat : string -> symbol
val real : string -> symbol
val hexa : string -> symbol
val binary : string -> symbol

(** {2 Terms} *)
val tType : term
val true_ : term
val false_ : term

val at_loc : loc:location -> term -> term
val column : ?loc:location -> term -> term -> term

val var : ?loc:location -> ?ty:term -> string -> term

val const : ?loc:location -> symbol -> term

val app : ?loc:location -> term -> term list -> term

val eq : ?loc:location -> term -> term -> term
val neq : ?loc:location -> term -> term -> term

val not_ : ?loc:location -> term -> term
val and_ : ?loc:location -> term list -> term
val or_ : ?loc:location -> term list -> term
val xor : ?loc:location -> term -> term -> term
val imply : ?loc:location -> term -> term -> term
val equiv : ?loc:location -> term -> term -> term
val forall : ?loc:location -> term list -> term -> term
val forall_ty : ?loc:location -> term list -> term -> term
val exists : ?loc:location -> term list -> term -> term
val letin : ?loc:location -> term list -> term -> term

val mk_fun_ty : ?loc:location -> term list -> term -> term

