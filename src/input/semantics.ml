
let log_section = Util.Section.make "syntax"
let log i fmt = Util.debug ~section:log_section i fmt

exception Extension_not_found of string

type extension = {
  name : string;
  descr : string;
  priority : int;
  builtins : Options.input -> Type.builtin_symbols;
  propagate_assert : string -> Expr.formula -> bool;
}

let exts = ref []
let active = ref []

let register
    ?(descr="") ?(priority=0)
    ?(tptp_builtins=(fun _ _ _ -> None))
    ?(smtlib_builtins=(fun _ _ _ -> None))
    ?(propagate_assert=(fun _ _ -> true)) name =
  exts := {
    name; descr; priority; propagate_assert;
    builtins = (function
        | Options.Tptp -> tptp_builtins
        | Options.Smtlib -> smtlib_builtins
        | _ -> (fun _ _ _ -> None));
  } :: !exts

let activate ext =
  let aux r = r.name = ext in
  try
    let r = CCList.find_pred_exn aux !exts in
    if not (List.exists aux !active) then
      active := List.merge (fun r r' -> compare r'.priority r.priority) [r] !active
    else
      log 0 "WARNING: Extension %s already activated" ext
  with Not_found ->
    raise (Extension_not_found ext)

let deactivate ext =
  let aux r = r.name = ext in
  try
    if not (List.exists aux !exts) then
      raise (Extension_not_found ext);
    let l1, l2 = List.partition aux !active in
    begin match l1 with
      | [] -> log 0 "WARNING: Extension %s already deactivated" ext
      | [r] -> active := l2
      | _ -> assert false
    end
  with Not_found ->
    raise (Extension_not_found ext)

let set_ext s =
  if s <> "" then
    match s.[0] with
    | '-' -> deactivate (String.sub s 1 (String.length s - 1))
    | '+' -> activate (String.sub s 1 (String.length s - 1))
    | _ -> activate s

let set_exts s =
  List.iter set_ext
    (List.map (fun (s, i, l) -> String.sub s i l) (CCString.Split.list_ ~by:"," s))

let log_active () =
  log 0 "active: %a" CCPrint.(list string) (List.map (fun r -> r.name) !active)

let doc_of_ext r = `I ("$(b," ^ r.name ^ ")", r.descr)

let ext_doc () =
  List.map doc_of_ext @@
  List.sort (fun r r' -> compare r.name r'.name) @@
  !exts

let type_env input_format =
  (fun s l l' ->
    let aux ext = ext.builtins input_format s l l' in
    CCList.find_map aux !active
  )

