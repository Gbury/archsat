
exception Parse_error of int

let parse_file file =
  try
    let res = Queue.create () in
    Queue.push (Ast.Sat (List.rev_map (List.rev_map Builtin.mk_prop) (Parsedimacs.parse file))) res;
    Queue.push Ast.CheckSat res;
    res
  with Parsedimacs.Syntax_error l ->
    raise (Parse_error l)

