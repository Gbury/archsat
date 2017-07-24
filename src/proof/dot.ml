
module D = Dispatcher

(* Printing wrappers *)
(* ************************************************************************ *)

let buffer = Buffer.create 1013

let sfmt =
  let fmt = Format.formatter_of_buffer buffer in
  let f = Format.pp_get_formatter_out_functions fmt () in
  let () = Format.pp_set_formatter_out_functions fmt
      Format.{ f with out_newline = function () ->
          f.out_string {|<br align="left" />|} 0 19}
  in
  fmt

let box pp x fmt () =
  let () = Buffer.clear buffer in
  let () = Format.fprintf sfmt "%a@?" pp x in
  let s = Buffer.contents buffer in
  Format.fprintf fmt "%s" s

let boxed pp = box pp ()

(* TODO: custom printers to avoid reserved DOT character sequences *)
let print_ty = Expr.Print.ty
let print_term = Expr.Print.term
let print_formula = Expr.Print.formula

(* Printing functor argument *)
(* ************************************************************************ *)

type _ D.msg +=
  | Info : D.lemma_info ->
    (string option * ((Format.formatter -> unit -> unit) list)) D.msg

module Arg = struct

  let print_atom fmt a =
    let f = a.Dispatcher.SolverTypes.lit in
    box Expr.Print.formula f fmt ()

  let hyp_info c =
    let id = CCOpt.get_exn @@ Solver.hyp_id c in
    "Hypothesis", Some "LIGHTBLUE",
    [fun fmt () -> Dolmen.Id.print fmt id]

  let lemma_info c =
    let lemma =
      match c.Dispatcher.SolverTypes.cpremise with
      | Dispatcher.SolverTypes.Lemma l -> l
      | _ -> assert false
    in
    let name = Format.sprintf "%s/%s" lemma.D.plugin_name lemma.D.proof_name in
    let color, fmts =
      match D.ask lemma.D.plugin_name (Info lemma.D.proof_info) with
      | Some r -> r
      | None -> None, [fun fmt () -> Format.fprintf fmt "N/A"]
    in
    name, color, List.map boxed fmts

  let assumption_info c =
    "assumption", Some "LIGHTBLUE", []

end

(* Printing proofs *)
(* ************************************************************************ *)

module P = Msat.Dot.Make(Solver.Proof)(Arg)

let print = P.print

