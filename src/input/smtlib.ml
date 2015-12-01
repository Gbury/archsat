
let translate c = c

let curr_p s_line buf =
  let loc = ParseLocation.of_lexbuf buf in
  ParseLocation.{
    loc with
    start_line = loc.start_line - s_line;
    stop_line = loc.stop_line - s_line;
  }

let parse_file f =
  let input = match f with
    | "stdin" -> stdin
    | _ -> open_in f
  in
  let buf = Lexing.from_channel input in
  ParseLocation.set_file buf f;
  let supplier = Parsesmtlib.MenhirInterpreter.lexer_lexbuf_to_supplier Lexsmtlib.token buf in
  let curr = ref [] in
  let loop = Parsesmtlib.MenhirInterpreter.loop supplier in
  let rec aux () =
     match !curr with
     | x :: r -> curr := r; Some (translate x)
     | [] ->
       let line = Lexing.(buf.lex_curr_p.pos_lnum) - 1 in
       begin match loop (Parsesmtlib.Incremental.input Lexing.(buf.lex_curr_p)) with
       | None -> None
       | Some l ->
         curr := l;
         aux ()
       | exception Parsesmtlib.Error ->
         let loc = curr_p line buf in
         Input.consume_line buf;
         raise (Input.Parsing_error (loc, "Parsing error"))
       | exception Lexsmtlib.Lexer_error ->
         let loc = curr_p line buf in
         Input.consume_line buf;
         raise (Input.Lexing_error loc)
       end
  in
  aux

