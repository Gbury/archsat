
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
        | In.Tptp -> tptp
        | In.Smtlib -> smtlib
        | In.Zf -> zf
        | _ -> default);
  }

module Addon = Extension.Make(struct
    type t = ext
    let neutral = mk_ext ()
    let section = Util.Section.make ~parent:Type.section "addons"
    let merge ~high ~low = {
      builtins = (fun input_format env ast id args ->
          Util.enter_prof section;
          let res = match high.builtins input_format env ast id args with
            | Some x -> Some x
            | None -> low.builtins input_format env ast id args
          in
          Util.exit_prof section;
          res);
    }
  end)

let type_env input = (Addon.get_res ()).builtins input

