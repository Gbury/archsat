(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Output functions *)
(* ************************************************************************ *)

module type Out = sig

  val prelude : Options.opts -> string

  val print_sat : Format.formatter -> Options.opts -> unit
  val print_unsat : Format.formatter -> Options.opts -> unit
  val print_unknown : Format.formatter -> Options.opts -> unit

  val print_exn : Options.opts -> Format.formatter -> exn -> unit

end

let get opt =
  match Options.(opt.output.format) with
  | Options.SZS -> (module Szs : Out)
  | Options.Standard -> (module Std : Out)

(* Output functions *)
(* ************************************************************************ *)

let prelude opt =
  let (module M) = get opt in
  M.prelude opt

let print_sat fmt opt =
  let (module M) = get opt in
  M.print_sat fmt opt

let print_unsat fmt opt =
  let (module M) = get opt in
  M.print_unsat fmt opt

let print_unknown fmt opt =
  let (module M) = get opt in
  M.print_unknown fmt opt

let print_exn opt fmt exn =
  let (module M) = get opt in
  M.print_exn opt fmt exn

