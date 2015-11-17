
(*
let section = Util.Section.make "builtin"
let log i fmt = Util.debug ~section i fmt
*)

(* Type builtins for languages *)
(* ************************************************************************ *)

let parse_tptp s args _ = match s with
  | "$o" -> Some (`Ty (Expr.Id.prop, args))
  | "$i" -> Some (`Ty (Expr.Id.base, args))
  | _ -> None

let parse_smtlib s args _ = match s with
  | "Bool" -> Some (`Ty (Expr.Id.prop, args))
  | _ -> None

;;
Semantics.Addon.register "base"
  ~descr:"Defines the base types/builtins of languages (such as tptp's $i and $o)"
  (Semantics.mk_ext ~tptp:parse_tptp ~smtlib:parse_smtlib ())
;;

(* Misc builtins *)
(* ************************************************************************ *)

module Misc = struct

  type Expr.builtin += Cast

  (* Casting *)
  let cast_cstr =
    let a = Expr.Id.ttype "a" in
    let ta = Expr.Ty.of_id a in
    let b = Expr.Id.ttype "b" in
    let tb = Expr.Ty.of_id b in
    Expr.Id.term_fun ~builtin:Cast "#cast" [a; b] [ta] tb

  let cast e ty =
    let ety = Expr.(e.t_type) in
    if Expr.Ty.equal ty ety then e
    else Expr.Term.apply cast_cstr [ety; ty] [e]

  (* Tuples *)
  let tuple_ty_cstr n =
    let name = string_of_int n ^ "-tuple" in
    Expr.Id.ty_fun name n

  let tuple_cstr =
    CCCache.with_cache (CCCache.unbounded 17)
      (fun n ->
         let name = string_of_int n ^ "-tuple" in
         let range = CCList.range 1 n in
         let vars = List.map (fun i -> Expr.Id.ttype ("type#" ^ string_of_int i)) range in
         let ty_args = List.map Expr.Ty.of_id vars in
         let ret = Expr.Ty.apply (tuple_ty_cstr n) ty_args in
         Expr.Id.term_fun name vars ty_args ret
      )

  let tuple l =
    let n = List.length l in
    let ty_l = List.map (fun t -> Expr.(t.t_type)) l in
    let f = tuple_cstr n in
    Expr.Term.apply f ty_l l

  (* Propositional calculus *)
  let p_true = Expr.Term.apply (Expr.Id.term_fun "true" [] [] Expr.Ty.prop) [] []
  let p_false = Expr.Term.apply (Expr.Id.term_fun "false" [] [] Expr.Ty.prop) [] []

  let prop_cache = CCCache.unbounded 128
  let mk_prop_aux = CCCache.with_cache prop_cache
      (fun i ->
         let c = Expr.Id.term_fun ("p" ^ string_of_int i) [] [] Expr.Ty.prop in
         Expr.Formula.pred (Expr.Term.apply c [] []))

  let mk_prop i =
    let p = mk_prop_aux (abs i) in
    if i >= 0 then p
    else Expr.Formula.neg p

  (* Absolute constants for types *)
  let const =
    let v = Expr.Id.ttype "a" in
    let c = Expr.Id.term_fun "#const" [v] [] (Expr.Ty.of_id v) in
    (fun ty -> Expr.Term.apply c [ty] [])

end

(* Arithmetic *)
(* ************************************************************************ *)

module Arith = struct

  exception Int_div

  (* Type definitions *)
  type ty = Int | Rat | Real

  type value =
    | Int of Z.t
    | Rat of Q.t
    | Real of Q.t Lazy.t

  type op =
    | Less | Lesseq
    | Greater | Greatereq
    | Minus (* unary minus *)
    | Sum | Difference
    | Product | Quotient

  type Expr.builtin +=
    | Type of ty
    | Val of value
    | Op of op

  type operator = ty -> Expr.ty Expr.function_descr Expr.id

  (* Operations on types *)
  let cmp_types (t: ty) (t': ty) =
    match t, t' with
    | Int, Int | Rat, Rat | Real, Real -> 0
    | Int, _ -> -1 | _, Int -> 1
    | Real, _ -> 1 | _, Real -> -1

  let max_type t t' = if cmp_types t t' > 0 then t else t'

  let add a b = match a, b with
    | Int z, Int z' -> Int Z.(z + z')
    | Rat q, Rat q' -> Rat Q.(q + q')
    | Real r, Real r' -> Real Q.(lazy (Lazy.force r + Lazy.force r'))
    | Int z, Rat q | Rat q, Int z -> Rat Q.(q + of_bigint z)
    | Int z, Real r | Real r, Int z -> Real Q.(lazy (Lazy.force r + of_bigint z))
    | Rat q, Real r | Real r, Rat q -> Real Q.(lazy (q + Lazy.force r))

  let mul a b = match a, b with
    | Int z, Int z' -> Int Z.(z * z')
    | Rat q, Rat q' -> Rat Q.(q * q')
    | Real r, Real r' -> Real Q.(lazy (Lazy.force r * Lazy.force r'))
    | Int z, Rat q | Rat q, Int z -> Rat Q.(q * of_bigint z)
    | Int z, Real r | Real r, Int z -> Real Q.(lazy (Lazy.force r * of_bigint z))
    | Rat q, Real r | Real r, Rat q -> Real Q.(lazy (q * Lazy.force r))

  (* Solver types for arithmetic *)
  let int_cstr = Expr.Id.ty_fun ~builtin:(Type Int) "Z" 0
  let rat_cstr = Expr.Id.ty_fun ~builtin:(Type Rat) "Q" 0
  let real_cstr = Expr.Id.ty_fun ~builtin:(Type Real) "R" 0

  let type_int = Expr.Ty.apply int_cstr []
  let type_rat = Expr.Ty.apply rat_cstr []
  let type_real = Expr.Ty.apply real_cstr []

  let to_ty (ty: ty) =
    match ty with
    | Int -> type_int
    | Rat -> type_rat
    | Real -> type_real

  let num_type = function
    | { Expr.t_type = {
        Expr.ty = Expr.TyApp ({
            Expr.builtin = Type ((Int | Rat | Real) as t)}, [])
      } } -> Some t
    | _ -> None

  (* Solver operator on arithmetic *)
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

  let dispatch (f_int, f_rat, f_real) (aty: ty) =
    match aty with Int -> f_int | Rat -> f_rat | Real -> f_real

  let less = dispatch @@ mk_pred2 ~builtin:(Op Less) "$less"
  let lesseq = dispatch @@ mk_pred2 ~builtin:(Op Lesseq) "$lesseq"
  let greater = dispatch @@ mk_pred2 ~builtin:(Op Greater) "$greater"
  let greatereq = dispatch @@ mk_pred2 ~builtin:(Op Greatereq) "$greatereq"

  let sum = dispatch @@ mk_binop ~builtin:(Op Sum) "$sum"
  let diff = dispatch @@ mk_binop ~builtin:(Op Difference) "$difference"
  let mult = dispatch @@ mk_binop ~builtin:(Op Product) "$product"
  let uminus = dispatch @@ mk_uop ~builtin:(Op Minus) "$uminus"

  let div_aux_q = mk_binary type_rat ~builtin:(Op Quotient) "$quotient"
  let div_aux_r = mk_binary type_real ~builtin:(Op Quotient) "$quotient"

  let div (aty: ty) = match aty with
    | Int -> raise Int_div
    | Rat -> div_aux_q
    | Real -> div_aux_r

  let div_e = dispatch @@ mk_binop "$quotient_e"
  let div_t = dispatch @@ mk_binop "$quotient_t"
  let div_f = dispatch @@ mk_binop "$quotient_f"

  let rem_e = dispatch @@ mk_binop "$remainder_e"
  let rem_t = dispatch @@ mk_binop "$remainder_t"
  let rem_f = dispatch @@ mk_binop "$remainder_f"

  let ceiling = dispatch @@ mk_uop "$ceiling"
  let truncate = dispatch @@ mk_uop "$truncate"
  let floor = dispatch @@ mk_uop "$floor"
  let round = dispatch @@ mk_uop "$round"

  let is_int = dispatch @@ mk_pred1 "$is_int"
  let is_rat = dispatch @@ mk_pred1 "$is_rat"
  let is_real = dispatch @@ mk_pred1 "$is_real"

  let rec bin_apply s = function
    | ([] | _ :: []) as l -> l
    | x :: y :: r -> (Expr.Term.apply s [] [x;y]) :: (bin_apply s r)

  let rec fold_apply s l =
    match bin_apply s l with
    | [] -> None
    | [e] -> Some e
    | r -> fold_apply s r

  let apply f l =
    match CCOpt.sequence_l (List.map num_type l) with
    | None -> None
    | Some l' ->
      let t = List.fold_left max_type Int l' in
      begin match fold_apply (f t) l with
        | None -> None
        | Some e -> Some e
      end

  (* Parsing arithmetic input *)
  let rec parse_int s pos base =
    let aux s pos acc =
      if pos >= 0 && pos < String.length s then begin
        match s.[pos] with
        | '0' .. '9' as c ->
          let n = Z.of_string (String.make 1 c) in
          parse_int s (pos + 1) Z.(acc * (of_int 10) + n)
        | _ -> acc, pos
      end else
        acc, pos
    in
    if pos >= String.length s then base, pos
    else match s.[pos] with
      | '-' ->
        let n, new_pos = aux s (pos + 1) base in
        Z.neg n, new_pos
      | _ -> aux s pos base

  let parse_number s start_pos =
    let n, pos = parse_int s start_pos Z.zero in
    if pos >= String.length s then Int n
    else begin match s.[pos] with
      | '/' ->
        if pos = start_pos then raise (Invalid_argument s)
        else begin
          let m, new_pos = parse_int s (pos + 1) Z.zero in
          if new_pos >= String.length s then Rat Q.(make n m)
          else raise (Invalid_argument s)
        end
      | '.' ->
        let pos = pos + 1 in
        let m, new_pos = parse_int s pos Z.zero in
        let exp = new_pos - pos in
        let r = lazy (Q.make n Z.(m / (pow (of_int 10) exp))) in
        if new_pos = String.length s then begin
          Real r
        end else begin match s.[new_pos] with
          | 'E' | 'e' ->
            let e, end_pos = parse_int s (new_pos + 1) Z.zero in
            if not (end_pos = String.length s) then raise (Invalid_argument s);
            let exp = Z.to_int e in
            Real (lazy (Q.make
                          (Z.pow (Lazy.force r).Q.num exp)
                          (Z.pow (Lazy.force r).Q.den exp)))
          | _ -> raise (Invalid_argument s)
        end
      | _ -> raise (Invalid_argument s)
    end

  let val_of_string s =
    if s = "" then None
    else
      try Some (parse_number s 0)
      with Invalid_argument _ -> None

  (*
  let q_of_val = function Int z -> Q.of_bigint z | Rat q -> q | Real r -> Lazy.force r
  let ty_of_val = function Int _ -> type_int | Rat _ -> type_rat | Real _ -> type_real
  *)

  let int_const = Hashtbl.create 42
  let rat_const = Hashtbl.create 42
  let real_const = Hashtbl.create 42

  let const_num s = function
    | Int i as v ->
      begin try
          Hashtbl.find int_const i
        with Not_found ->
          let res = Expr.Id.term_fun ~builtin:(Val v) s [] [] type_int in
          Hashtbl.add int_const i res;
          res
      end
    | Rat q as v ->
      begin try
          Hashtbl.find rat_const q
        with Not_found ->
          let res = Expr.Id.term_fun ~builtin:(Val v) s [] [] type_rat in
          Hashtbl.add rat_const q res;
          res
      end
    | Real _ as v ->
      begin try
          Hashtbl.find real_const s
        with Not_found ->
          let res = Expr.Id.term_fun ~builtin:(Val v) s [] [] type_real in
          Hashtbl.add real_const s res;
          res
      end

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
        (fun opt -> `Term (Misc.cast_cstr, [to_ty opt; ret], t_args))
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
    | "$quotient_e" -> aux div_e
    | "$quotient_t" -> aux div_t
    | "$quotient_f" -> aux div_f
    | "$remainder_e" -> aux rem_e
    | "$remainder_t" -> aux rem_t
    | "$remainder_f" -> aux rem_f
    | "$floor" -> aux floor
    | "$ceiling" -> aux ceiling
    | "$truncate" -> aux truncate
    | "$round" -> aux round
    | "$is_int" -> aux is_int
    | "$is_rat" -> aux is_rat
    | "$is_real" -> aux is_real
    | "$to_int" when ty_args = [] -> aux_cast type_int
    | "$to_rat" when ty_args = [] -> aux_cast type_rat
    | "$to_real" when ty_args = [] -> aux_cast type_real
    | _ -> begin match val_of_string s with
        | Some value -> Some (`Term (const_num s value, ty_args, t_args))
        | None -> None
      end

end

;;
Semantics.Addon.register "arith"
  ~descr:"Builtin symbols for arithmetic, and arithmetic constants of arbitrary precision"
  (Semantics.mk_ext ~tptp:Arith.parse_tptp ())
;;

