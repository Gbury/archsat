
(* Output functions *)
(* ************************************************************************ *)

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

let print_timeout opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_timeout opt opt.Options.out
  | Options.Standard -> Std.print_timeout opt opt.Options.out

let print_spaceout opt =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_spaceout opt opt.Options.out
  | Options.Standard -> Std.print_spaceout opt opt.Options.out

let print_exn opt exn =
  match opt.Options.output_format with
  | Options.SZS -> Szs.print_exn opt opt.Options.out exn
  | Options.Standard -> Std.print_exn opt opt.Options.out exn

