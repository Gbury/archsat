
(* Typing *)
(* ************************************************************************ *)

let i_cstr = Expr.type_const "$i" 0
let type_i = Expr.type_app i_cstr []

(* Tuples *)
(* ************************************************************************ *)

module H = Hashtbl.Make(struct type t = int let hash i = i land max_int let equal = (=) end)
let tuples = H.create 17

let tuple_ty_cstr n =
  let name = string_of_int n ^ "-tuple" in
  Expr.type_const name n

let tuple_cstr n =
  try
    H.find tuples n
  with Not_found ->
    let name = string_of_int n ^ "-tuple" in
    let range = CCList.range 1 n in
    let vars = List.map (fun i -> Expr.ttype_var ("type#" ^ string_of_int i)) range in
    let ty_args = List.map Expr.type_var vars in
    let ret = Expr.type_app (tuple_ty_cstr n) ty_args in
    let res = Expr.term_const name vars ty_args ret in
    H.add tuples n res;
    res

let tuple l =
  let n = List.length l in
  let ty_l = List.map (fun t -> Expr.(t.t_type)) l in
  let f = tuple_cstr n in
  Expr.term_app f ty_l l

(* Propositional calculus *)
(* ************************************************************************ *)

let p_true = Expr.term_app (Expr.term_const "true" [] [] Expr.type_prop) [] []
let p_false = Expr.term_app (Expr.term_const "false" [] [] Expr.type_prop) [] []

let mk_prop i =
  let aux i =
    let c = Expr.term_const ("p" ^ string_of_int i) [] [] Expr.type_prop in
    Expr.f_pred (Expr.term_app c [] [])
  in
  if i >= 0 then
    aux i
  else
    Expr.f_not (aux ~-i)


