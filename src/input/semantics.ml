(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Semantic extensions *)
(* ************************************************************************ *)

let section = Section.make ~parent:Type.section "addons"

type ext = {
  builtins : In.language -> Type.builtin_symbols;
}

let default = fun _ _ _ _ -> None

let mk_ext
    ?(tptp=default)
    ?(smtlib=default)
    ?(zf=default)
    () =
  { builtins = (function
        | In.Dimacs | In.ICNF -> default
        | In.Smtlib -> smtlib
        | In.Tptp -> tptp
        | In.Zf -> zf
      );
  }

(* Addons *)
(* ************************************************************************ *)

(* Instantiate the extension functor *)
module Addon = Extension.Make(struct
    type t = ext
    let section = section
    let neutral = mk_ext ()
    let merge ~high ~low = {
      builtins = (fun input_format env ast id args ->
          match high.builtins input_format env ast id args with
          | Some x -> Some x
          | None -> low.builtins input_format env ast id args
        );
    }
  end)

(* Convenience function to get the builtin function for type-checking *)
let type_env input =
  let f = (Addon.get_res ()).builtins input in
  (fun env ast id args ->
     Util.enter_prof section;
     let res = f env ast id args in
     Util.exit_prof section;
     res)

