
(* Type definitions *)
(* ************************************************************************ *)

type location = ParseLocation.t

type symbol =
  | Int of string
  | Rat of string
  | Real of string
  | String of string
  | Ttype | Wildcard
  | True | False
  | Eq | Distinct | Arrow
  | All | AllTy | Ex
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

type command =
  | Sat of Expr.Formula.t list list     (** Special case for dimacs input *)
  | Push of int                         (** Push *)
  | Pop of int                          (** Pop *)
  | TypeDef of string * symbol * term   (** Type definition *)
  | Alias of symbol * term list * term  (** Alias (smtlib style) *)
  | Assert of string * term             (** Add term to the assertions *)
  | CheckSat                            (** Check-sat *)


(* Printing *)
(* ************************************************************************ *)

let print_command_name fmt = function
  | Sat _ -> Format.fprintf fmt "Cnf-assume (dimacs)"
  | Push _ -> Format.fprintf fmt "Push"
  | Pop _ -> Format.fprintf fmt "Pop"
  | TypeDef _ -> Format.fprintf fmt "Type definition"
  | Alias _ -> Format.fprintf fmt "Alias binding"
  | Assert _ -> Format.fprintf fmt "Assert"
  | CheckSat -> Format.fprintf fmt "Check-sat"

(* Symbol making *)
(* ************************************************************************ *)

let wildcard = Wildcard
let distinct = Distinct

let int s = Int s
let rat s = Rat s
let real s = Real s
let sym s = String s

(* Term making *)
(* ************************************************************************ *)

let make ?loc descr =
  { loc = loc; term = descr; }

let at_loc ~loc t =
  { t with loc = Some loc; }

let const ?loc s = make ?loc (Const s)

let tType = const Ttype
let true_ = const True
let false_ = const False

let var ?loc ?ty s = match ty with
  | None -> make ?loc (Var s)
  | Some t -> make ?loc (Column (make ?loc (Var s), t))

let app ?loc f l = make ?loc (App (f, l))

let not_ ?loc f = app ?loc (const Not) [f]

let eq ?loc a b = app ?loc (const Eq) [a; b]

let neq ?loc a b = not_ ?loc (eq ?loc a b)

let and_ ?loc l = app ?loc (const And) l

let or_ ?loc l = app ?loc (const Or) l

let xor ?loc p q = app ?loc (const Xor) [p; q]

let imply ?loc p q = app ?loc (const Imply) [p; q]

let equiv ?loc p q = app ?loc (const Equiv) [p; q]

let forall ?loc vars f = make ?loc (Binding (All, vars, f))

let forall_ty ?loc vars f = make ?loc (Binding (AllTy, vars, f))

let exists ?loc vars f = make ?loc (Binding (Ex, vars, f))

let mk_fun_ty ?loc args ret = app ?loc (const Arrow) (ret :: args)


