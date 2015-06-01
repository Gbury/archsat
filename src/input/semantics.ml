
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
    let log_name = "addons"
    let merge l = {
      builtins = (fun input_format s args arg' ->
        let aux ext = ext.builtins input_format s args arg' in
        CCList.find_map aux l);
    }
  end)

let type_env = (Addon.get_res ()).builtins

