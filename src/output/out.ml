
(* Output functions *)
(* ************************************************************************ *)

let prelude opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.prelude opt
  | Options.Standard -> Std.prelude opt

let print_sat opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_sat opt opt.Options.out
  | Options.Standard -> Std.print_sat opt opt.Options.out

let print_unsat opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_unsat opt opt.Options.out
  | Options.Standard -> Std.print_unsat opt opt.Options.out

let print_unknown opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_unknown opt opt.Options.out
  | Options.Standard -> Std.print_unknown opt opt.Options.out

let print_exn opt exn =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_exn opt opt.Options.out exn
  | Options.Standard -> Std.print_exn opt opt.Options.out exn

