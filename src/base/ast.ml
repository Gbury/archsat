
(* Type definitions *)
(* ************************************************************************ *)

type location = ParseLocation.t

type symbol =
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

type command =
  | Push                                    (** Push *)
  | Pop                                     (** Pop *)
  | Cnf of Expr.Formula.t list list         (** Special case for dimacs input *)
  | NewType of string * symbol * int        (** New type constructor *)
  | TypeDef of string * symbol * term       (** Type definition *)
  | TypeAlias of symbol * term list * term  (** Type alias (smtlib style) *)
  | Alias of symbol * term list * term      (** Alias (smtlib style) *)
  | Assert of string * term * bool          (** Add term to the assertions *)
  | CheckSat                                (** Check-sat *)
  | Exit                                    (** Exit the prover *)


(* Printing *)
(* ************************************************************************ *)

let debug_symbol b = function
  | String s -> Printf.bprintf b "%s" s
  | Ttype -> Printf.bprintf b "tType"
  | Wildcard -> Printf.bprintf b "_"
  | True -> Printf.bprintf b "True"
  | False -> Printf.bprintf b "False"
  | Eq -> Printf.bprintf b "="
  | Distinct -> Printf.bprintf b "Distinct"
  | Ite -> Printf.bprintf b "Ite"
  | Arrow -> Printf.bprintf b "->"
  | All -> Printf.bprintf b "Forall"
  | AllTy -> Printf.bprintf b "ForallTy"
  | Ex -> Printf.bprintf b "Exists"
  | Let -> Printf.bprintf b "Let"
  | And -> Printf.bprintf b "/\\"
  | Or -> Printf.bprintf b "\\/"
  | Xor -> Printf.bprintf b "xor"
  | Imply -> Printf.bprintf b "=>"
  | Equiv -> Printf.bprintf b "<=>"
  | Not -> Printf.bprintf b "Not"

let rec print_list_pre f sep b = function
  | [] -> ()
  | x :: r ->
    Printf.bprintf b "%s%a" sep f x;
    print_list_pre f sep b r

let rec debug_term b t = match t.term with
  | Var s -> Printf.bprintf b "%s" s
  | Column (t1, t2) -> Printf.bprintf b "%a:%a" debug_term t1 debug_term t2
  | Const sym -> Printf.bprintf b "{%a}" debug_symbol sym
  | App (f, l) ->
    Printf.bprintf b "(%a%a)" debug_term f (print_list_pre debug_term " ") l
  | Binding (sym, l, p) ->
    Printf.bprintf b "%a:%a.%a" debug_symbol sym
      (print_list_pre debug_term " ") l debug_term p

let s_term t = CCPrint.to_string debug_term t

let print_command_name fmt = function
  | Cnf _ -> Format.fprintf fmt "Cnf-assume (dimacs)"
  | Push -> Format.fprintf fmt "Push"
  | Pop -> Format.fprintf fmt "Pop"
  | NewType _ -> Format.fprintf fmt "New type"
  | TypeDef _ -> Format.fprintf fmt "Type definition"
  | TypeAlias _ -> Format.fprintf fmt "Type aliasing"
  | Alias _ -> Format.fprintf fmt "Alias binding"
  | Assert _ -> Format.fprintf fmt "Assert"
  | CheckSat -> Format.fprintf fmt "Check-sat"
  | Exit -> Format.fprintf fmt "Exit"

(* Symbol making *)
(* ************************************************************************ *)

let wildcard = Wildcard
let distinct = Distinct

let int s = String s
let rat s = String s
let real s = String s
let sym s = String s
let hexa s = String s
let binary s = String s

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

let column ?loc s t = make ?loc (Column (s, t))

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

let letin ?loc bindings t = make ?loc (Binding (Let, bindings, t))

let forall ?loc vars f = make ?loc (Binding (All, vars, f))

let forall_ty ?loc vars f = make ?loc (Binding (AllTy, vars, f))

let exists ?loc vars f = make ?loc (Binding (Ex, vars, f))

let mk_fun_ty ?loc args ret = app ?loc (const Arrow) (ret :: args)


