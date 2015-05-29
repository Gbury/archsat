
module M = Map.Make(Q)

(* Type extension for builtin operators *)
(* ************************************************************************ *)

type arith_type = Int | Rat | Real

type arith_val = Int of Z.t | Rat of Q.t | Real of Q.t

type arith_op =
  | Less | Lesseq | Greater | Greatereq
  | Sum | Difference | Product | Quotient

type arith_builtin =
  | Type of arith_type
  | Val of arith_val
  | Op of arith_op

type Expr.builtin += Arith of arith_builtin

(* Arithmetic types *)
(* ************************************************************************ *)

let type_int = Expr.Ty.apply (Expr.Id.ty_fun ~builtin:(Arith (Type Int)) "Z" 0) []
let type_rat = Expr.Ty.apply (Expr.Id.ty_fun ~builtin:(Arith (Type Rat)) "Q" 0) []
let type_real = Expr.Ty.apply (Expr.Id.ty_fun ~builtin:(Arith (Type Real)) "R" 0) []

let num_type = function
  | { Expr.t_type = {
      Expr.ty = Expr.TyApp ({
          Expr.builtin = Arith (Type ((Int | Rat | Real) as t))}, [])
    } } -> Some t
  | _ -> None

let mk_pred ?builtin args name =
  Expr.Id.term_fun ?builtin name [] args Expr.Ty.prop

let mk_int2_pred ?builtin name = mk_pred ?builtin [type_int; type_int] name
let mk_rat2_pred ?builtin name = mk_pred ?builtin [type_rat; type_rat] name
let mk_real2_pred ?builtin name = mk_pred ?builtin [type_real; type_real] name

let mk_pred2 ?builtin name =
  mk_int2_pred ?builtin name,
  mk_rat2_pred ?builtin name,
  mk_real2_pred ?builtin name

let mk_binary ty ?builtin name = Expr.Id.term_fun ?builtin name [] [ty; ty] ty

let mk_binop ?builtin name =
  mk_binary type_int ?builtin name,
  mk_binary type_rat ?builtin name,
  mk_binary type_real ?builtin name

let dispatch args =
  let aux (f_int, f_rat, f_real) (aty: arith_type) =
    match aty with Int -> `Term f_int | Rat -> `Term f_rat | Real -> `Term f_real
  in
  CCOpt.map (aux args)

(* Arithmetic Operators *)
(* ************************************************************************ *)

let less = dispatch @@ mk_pred2 ~builtin:(Arith (Op Less)) "$less"
let lesseq = dispatch @@ mk_pred2 ~builtin:(Arith (Op Lesseq)) "$lesseq"
let greater = dispatch @@ mk_pred2 ~builtin:(Arith (Op Greater)) "$greater"
let greatereq = dispatch @@ mk_pred2 ~builtin:(Arith (Op Greatereq)) "$greatereq"

let sum = dispatch @@ mk_binop ~builtin:(Arith (Op Sum)) "$sum"
let diff = dispatch @@ mk_binop ~builtin:(Arith (Op Difference)) "$difference"
let mult = dispatch @@ mk_binop ~builtin:(Arith (Op Product)) "$product"
let div = dispatch @@ mk_binop ~builtin:(Arith (Op Quotient)) "$quotient"

(* Parse a number *)
(* ************************************************************************ *)

let val_of_string s =
  let rec parse_int s pos acc =
    if pos >= 0 && pos < String.length s then begin
      match s.[pos] with
      | '0' .. '9' as c ->
        let n = Z.of_string (String.make 1 c) in
        parse_int s (pos + 1) Z.(acc * (of_int 10) + n)
      | _ -> acc, pos
    end else
      acc, pos
  in
  let parse_number s start_pos =
    let n, pos = parse_int s start_pos Z.zero in
    if pos >= String.length s then Int n
    else begin match s.[pos] with
      | '/' ->
        if pos = start_pos then raise (Invalid_argument s)
        else begin
          let m, end_pos = parse_int s pos Z.zero in
          if end_pos = String.length s then Rat Q.(make n m)
          else raise (Invalid_argument s)
        end
      | '.' ->
        let pos = pos + 1 in
        let m, end_pos = parse_int s pos Z.zero in
        if end_pos = String.length s then begin
          let exp = end_pos - pos in
          Real (Q.make n Z.(m / (pow (of_int 10) exp)))
        end else raise (Invalid_argument s)
      | _ -> raise (Invalid_argument s)
    end
  in
  try
    if s = "" then None
    else begin match s.[0] with
      | '-' -> begin match parse_number s 1 with
          | Int z -> Some (Int (Z.neg z))
          | Rat q -> Some (Rat (Q.neg q))
          | Real r -> Some (Real (Q.neg r))
        end
      | _ -> Some (parse_number s 0)
    end
  with Invalid_argument _ -> None

let q_of_val = function Int z -> Q.of_bigint z | Rat q -> q | Real r -> r
let ty_of_val = function Int _ -> type_int | Rat _ -> type_rat | Real _ -> type_real

let const_map = ref M.empty

let const_num v =
  let q = q_of_val v in
  try
    `Term (M.find q !const_map)
  with Not_found ->
    let res = Expr.Id.term_fun ~builtin:(Arith (Val v)) (Q.to_string q) [] [] (ty_of_val v) in
    const_map := M.add q res !const_map;
    `Term res

(* Parse tptp input *)
(* ************************************************************************ *)

let list_type l =
  let rec aux = function
    | [Some ty] -> Some ty
    | (Some ty) :: (((Some ty') :: _) as r) when ty = ty' -> aux r
    | _ -> None
  in
  aux (List.map num_type l)

let parse_tptp s ty_args t_args =
  match s with
  | "$less" -> less (list_type t_args)
  | "$lesseq" -> lesseq (list_type t_args)
  | "$greater" -> greater (list_type t_args)
  | "$greatereq" -> greatereq (list_type t_args)
  | "$sum" -> sum (list_type t_args)
  | "$difference" -> diff (list_type t_args)
  | "$product" -> mult (list_type t_args)
  | "$quotient" -> div (list_type t_args)
  | _ -> CCOpt.map const_num (val_of_string s)


(* Register semantic typing *)
(* ************************************************************************ *)
;;
Semantics.register
  ~descr:"Semantics and Typing of arithmetic"
  ~tptp_builtins:parse_tptp
  "arith"

