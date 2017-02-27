
(* Output functions *)
(* ************************************************************************ *)

let prelude opt =
  match Options.(opt.output.format) with
  | Options.SZS -> Szs.prelude opt
  | Options.Standard -> Std.prelude opt

let print_sat opt =
  match Options.(opt.output.format) with
  | Options.SZS -> Szs.print_sat opt Options.(opt.output.fmt)
  | Options.Standard -> Std.print_sat opt Options.(opt.output.fmt)

let print_unsat opt =
  match Options.(opt.output.format) with
  | Options.SZS -> Szs.print_unsat opt Options.(opt.output.fmt)
  | Options.Standard -> Std.print_unsat opt Options.(opt.output.fmt)

let print_unknown opt =
  match Options.(opt.output.format) with
  | Options.SZS -> Szs.print_unknown opt Options.(opt.output.fmt)
  | Options.Standard -> Std.print_unknown opt Options.(opt.output.fmt)

let print_exn opt fmt exn =
  match Options.(opt.output.format) with
  | Options.SZS -> Szs.print_exn opt fmt exn
  | Options.Standard -> Std.print_exn opt fmt exn

