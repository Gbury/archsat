
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

let register () =
  Dispatcher.Plugin.register "arith"
    ~descr:"Handles satisfiability of arithmetic formulas (work in progress, DO NOT USE)."
    (Dispatcher.mk_ext ~section ())

