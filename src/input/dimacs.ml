
exception Parse_error of int

let parse_file file =
  try
    let l = Parsedimacs.parse file in
    let cnf = List.rev_map (List.rev_map Builtin.Misc.mk_prop) l in
    Gen.of_list [Ast.Cnf cnf; Ast.CheckSat]
  with Parsedimacs.Syntax_error l ->
    raise (Parse_error l)

