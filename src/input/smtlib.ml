
exception Parse_error of ParseLocation.t * string

let translate c = c

(* raise a readable parse error *)
let _raise_error msg lexbuf =
  let loc = ParseLocation.of_lexbuf lexbuf in
  raise (Parse_error (loc, msg))

let parse_file f =
  let input = match f with
    | "stdin" -> stdin
    | _ -> open_in f
  in
  let buf = Lexing.from_channel input in
  ParseLocation.set_file buf f;
  let supplier = Parsesmtlib.MenhirInterpreter.lexer_lexbuf_to_supplier Lexsmtlib.token buf in
  let curr = ref [] in
  let rec aux () =
     match !curr with
     | x :: r -> curr := r; Some (translate x)
     | [] -> begin match Parsesmtlib.MenhirInterpreter.loop supplier
                           (Parsesmtlib.Incremental.input buf.Lexing.lex_curr_p) with
       | None -> None
       | Some l -> curr := l; aux ()
       | exception Parsesmtlib.Error -> _raise_error "Parsing error" buf
       end
  in
  aux

