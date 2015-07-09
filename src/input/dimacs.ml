
exception Parse_error of int

let parse_file file =
  try
    let res = Queue.create () in
    let l = Parsedimacs.parse file in
    let cnf = List.rev_map (List.rev_map Builtin.Misc.mk_prop) l in
    Queue.push (Ast.Sat cnf) res;
    Queue.push Ast.CheckSat res;
    res
  with Parsedimacs.Syntax_error l ->
    raise (Parse_error l)

