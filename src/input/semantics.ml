
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
    let dummy = mk_ext ()
    let section = Util.Section.make ~parent:Type.section "addons"
    let merge l = {
      builtins = (fun input_format s args arg' ->
          Util.enter_prof section;
          let aux ext = ext.builtins input_format s args arg' in
          let res = CCList.find_map aux l in
          Util.exit_prof section;
          res);
    }
  end)

let type_env input = (Addon.get_res ()).builtins input

