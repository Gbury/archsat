
let section = Section.make ~parent:Dispatcher.section "arith"

module B = Builtin.Arith

(* Type definitions *)
(* ************************************************************************ *)

type bound =
  | Strict of Q.t
  | Large of Q.t

type interval = {
  inf: bound;
  upp: bound;
}

type domain = interval list
(** Intervals in a domain should be non-overlapping and ordered in ascending order. *)

(* Domain checking *)
(* ************************************************************************ *)

module E = Backtrack.Hashtbl(Expr.Term)

let h : domain E.t = E.create Dispatcher.stack

let val_to_q = function
  | B.Int z -> Q.of_bigint z
  | B.Rat q -> q
  | B.Real q -> Lazy.force q

let evaluate_aux t =
  Arith.M.fold (fun e c acc ->
      match Dispatcher.get_assign e with
      | { Expr.term = Expr.App ({ Expr.builtin = B.Val v}, [], []) } ->
        CCOpt.map (fun acc -> Q.(acc + c * val_to_q v)) acc
      | _ -> None
    ) t.Arith.Lit.sum (Some (val_to_q t.Arith.Lit.const))

let evaluate t = CCOpt.map evaluate_aux @@ Arith.Lit.parse_num t

(* Incomplete extension *)
(* ************************************************************************ *)

let is_arith_term = function
  | { Expr.term = Expr.App ({ Expr.builtin = Builtin.Arith.Op _ }, _, _)} ->
    true
  | _ -> false

let rec is_arith_formula = function
  | { Expr.formula = Expr.Pred t } -> is_arith_term t
  | { Expr.formula = Expr.Equal (a, b) } -> is_arith_term a || is_arith_term b
  | { Expr.formula = Expr.Not f } -> is_arith_formula f
  | _ -> false

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Solver.Found_sat seq ->
    if Sequence.exists is_arith_formula seq then
      Some Solver.Incomplete
    else
      Some Solver.Sat_ok
  | _ -> None

let register () =
  Dispatcher.Plugin.register "arith"
    ~descr:"Handles satisfiability of arithmetic formulas (work in progress, DO NOT USE)."
    (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle=handle} ())

