
module M = Map.Make(Q)

let log_section = Util.Section.make "arith"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type extension for builtin operators *)
(* ************************************************************************ *)

type arith_type = Int | Rat | Real

type arith_val = Int of Z.t | Rat of Q.t | Real of Q.t

type arith_op =
  | Less | Lesseq
  | Greater | Greatereq
  | Minus (* unary minus *)
  | Sum | Difference
  | Product | Quotient

type arith_builtin =
  | Type of arith_type
  | Val of arith_val
  | Op of arith_op

type Expr.builtin += Arith of arith_builtin

(* Arithmetic types *)
(* ************************************************************************ *)

let int_cstr = Expr.Id.ty_fun ~builtin:(Arith (Type Int)) "Z" 0
let rat_cstr = Expr.Id.ty_fun ~builtin:(Arith (Type Rat)) "Q" 0
let real_cstr = Expr.Id.ty_fun ~builtin:(Arith (Type Real)) "R" 0

let type_int = Expr.Ty.apply int_cstr []
let type_rat = Expr.Ty.apply rat_cstr []
let type_real = Expr.Ty.apply real_cstr []

let to_ty (ty: arith_type) =
  match ty with
  | Int -> type_int
  | Rat -> type_rat
  | Real -> type_real

let num_type = function
  | { Expr.t_type = {
      Expr.ty = Expr.TyApp ({
          Expr.builtin = Arith (Type ((Int | Rat | Real) as t))}, [])
    } } -> Some t
  | _ -> None

let mk_pred ?builtin args name =
  Expr.Id.term_fun ?builtin name [] args Expr.Ty.prop

let mk_pred1 ?builtin name =
  mk_pred ?builtin [type_int] name,
  mk_pred ?builtin [type_rat] name,
  mk_pred ?builtin [type_real] name

let mk_pred2 ?builtin name =
  mk_pred ?builtin [type_int; type_int] name,
  mk_pred ?builtin [type_rat; type_rat] name,
  mk_pred ?builtin [type_real; type_real] name

let mk_unary ty ?builtin name = Expr.Id.term_fun ?builtin name [] [ty] ty
let mk_binary ty ?builtin name = Expr.Id.term_fun ?builtin name [] [ty; ty] ty

let mk_uop ?builtin name =
  mk_unary type_int ?builtin name,
  mk_unary type_rat ?builtin name,
  mk_unary type_real ?builtin name

let mk_binop ?builtin name =
  mk_binary type_int ?builtin name,
  mk_binary type_rat ?builtin name,
  mk_binary type_real ?builtin name

let dispatch (f_int, f_rat, f_real) (aty: arith_type) =
  match aty with Int -> f_int | Rat -> f_rat | Real -> f_real

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
let uminus = dispatch @@ mk_uop ~builtin:(Arith (Op Minus)) "$uminus"

let is_int = dispatch @@ mk_pred1 "$is_int"
let is_rat = dispatch @@ mk_pred1 "$is_rat"
let is_real = dispatch @@ mk_pred1 "$is_real"

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
          let m, end_pos = parse_int s (pos + 1) Z.zero in
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
  with Invalid_argument _ ->
    log 1 "failed to parse string : %s" s;
      None

let q_of_val = function Int z -> Q.of_bigint z | Rat q -> q | Real r -> r
let ty_of_val = function Int _ -> type_int | Rat _ -> type_rat | Real _ -> type_real

let const_map = ref M.empty

let const_num v =
  let q = q_of_val v in
  try
    M.find q !const_map
  with Not_found ->
    let res = Expr.Id.term_fun ~builtin:(Arith (Val v)) (Q.to_string q) [] [] (ty_of_val v) in
    const_map := M.add q res !const_map;
    res

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
  let aux f = CCOpt.map
      (fun opt -> `Term (f opt, ty_args, t_args))
      (list_type t_args)
  in
  let aux_cast ret = CCOpt.map
      (fun opt -> `Term (Builtin.cast_cstr, [to_ty opt; ret], t_args))
      (list_type t_args)
  in
  match s with
  | "$int" -> Some (`Ty (int_cstr, ty_args))
  | "$rat" -> Some (`Ty (rat_cstr, ty_args))
  | "$real" -> Some (`Ty (real_cstr, ty_args))
  | "$less" -> aux less
  | "$lesseq" -> aux lesseq
  | "$greater" -> aux greater
  | "$greatereq" -> aux greatereq
  | "$uminus" -> aux uminus
  | "$sum" -> aux sum
  | "$difference" -> aux diff
  | "$product" -> aux mult
  | "$quotient" -> aux div
  | "$is_int" -> aux is_int
  | "$is_rat" -> aux is_rat
  | "$is_real" -> aux is_real
  | "$to_int" when ty_args = [] -> aux_cast type_int
  | "$to_rat" when ty_args = [] -> aux_cast type_rat
  | "$to_real" when ty_args = [] -> aux_cast type_real
  | _ -> begin match val_of_string s with
      | Some value -> Some (`Term (const_num value, ty_args, t_args))
      | None -> None
    end


(* Register semantic typing *)
(* ************************************************************************ *)
;;
Semantics.register
  ~descr:"Builtin symbols for arithmetic, and arithmetic constants of arbitrary precision"
  ~tptp_builtins:parse_tptp
  "arith"

