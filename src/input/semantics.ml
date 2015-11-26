
type ext = {
  builtins : Options.input -> Type.builtin_symbols;
}

let default = fun _ _ _ -> None

let mk_ext ?(tptp=default) ?(smtlib=default) () =
  { builtins = (function
        | Options.Tptp -> tptp
        | Options.Smtlib -> smtlib
        | _ -> default);
  }

module Addon = Extension.Make(struct
    type t = ext
    let neutral = mk_ext ()
    let section = Util.Section.make ~parent:Type.section "addons"
    let merge ~high ~low = {
      builtins = (fun input_format s args arg' ->
          Util.enter_prof section;
          let res = match high.builtins input_format s args arg' with
            | Some x -> Some x
            | None -> low.builtins input_format s args arg'
          in
          Util.exit_prof section;
          res);
    }
  end)

let type_env input = (Addon.get_res ()).builtins input

