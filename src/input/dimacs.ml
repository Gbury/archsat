
exception Parse_error of int

let parse_file file =
    try
        List.rev_map (List.rev_map Sat.mk_prop) (Parsedimacs.parse file)
    with Parsedimacs.Syntax_error l ->
      raise (Parse_error l)

