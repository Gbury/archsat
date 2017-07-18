
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

let ppify pp x = fun fmt () ->
  let () = Buffer.clear buffer in
  let () = Format.fprintf sfmt "%a@?" pp x in
  let s = Buffer.contents buffer in
  Format.fprintf fmt "%s" s

(* TODO: custom printers to avoid reserved DOT character sequences *)
let print_ty fmt ty = ppify Expr.Print.ty ty fmt ()
let print_term fmt t = ppify Expr.Print.term t fmt ()
let print_formula fmt f = ppify Expr.Print.formula f fmt ()

(* Printing functor argument *)
(* ************************************************************************ *)

module Arg = struct

  let print_atom = print_formula

  let lemma_info l =
    let name = Format.sprintf "%s/%s" l.D.plugin_name l.D.proof_name in
    let color =
      match l.D.plugin_name with
      | "meta" | "inst" -> Some "purple"
      | "rwrt" -> Some "red"
      | _ -> Some "blue"
    in
    let fmts =
      List.map (ppify print_ty) l.D.proof_ty_args @
      List.map (ppify print_term) l.D.proof_term_args @
      List.map (ppify print_formula) l.D.proof_formula_args
    in
    name, color, fmts

end

(* Printing proofs *)
(* ************************************************************************ *)

module P = Msat.Dot.Simple(Solver.Proof)(Arg)

let print = P.print

