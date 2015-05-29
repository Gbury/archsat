
(* Builtin symbols *)
(* ************************************************************************ *)

type Expr.builtin += Cast

(* Typing *)
(* ************************************************************************ *)

(* Type $i *)
let i_cstr = Expr.Id.ty_fun "$i" 0
let type_i = Expr.Ty.apply i_cstr []

(* Casting *)
let cast_cstr =
  let a = Expr.Id.ttype "a" in
  let ta = Expr.Ty.of_id a in
  let b = Expr.Id.ttype "b" in
  let tb = Expr.Ty.of_id b in
  Expr.Id.term_fun ~builtin:Cast "#cast" [a; b] [ta] tb

let cast e t =
  let ty = Expr.(e.t_type) in
  Expr.Term.apply cast_cstr [ty; t] [e]

(* Tuples *)
(* ************************************************************************ *)

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
(* ************************************************************************ *)

let p_true = Expr.Term.apply (Expr.Id.term_fun "true" [] [] Expr.Ty.prop) [] []
let p_false = Expr.Term.apply (Expr.Id.term_fun "false" [] [] Expr.Ty.prop) [] []

let mk_prop i =
  let aux = CCCache.with_cache (CCCache.unbounded 128)
      (fun i ->
         let c = Expr.Id.term_fun ("p" ^ string_of_int i) [] [] Expr.Ty.prop in
         Expr.Formula.pred (Expr.Term.apply c [] []))
  in
  if i >= 0 then
    aux i
  else
    Expr.Formula.neg (aux ~-i)

(* Absolute constants for types *)
(* ************************************************************************ *)

let const =
  let v = Expr.Id.ttype "a" in
  let c = Expr.Id.term_fun "#const" [v] [] (Expr.Ty.of_id v) in
  (fun ty -> Expr.Term.apply c [ty] [])

