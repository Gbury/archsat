
exception Parse_error of ParseLocation.t * string

let translate c = c

let parse_file f =
  let input = match f with
    | "stdin" -> stdin
    | _ -> open_in f
  in
  let buf = Lexing.from_channel input in
  ParseLocation.set_file buf f;
  let supplier = Parsesmtlib.MenhirInterpreter.lexer_lexbuf_to_supplier Lexsmtlib.token buf in
  let curr = ref [] in
  let loop = Parsesmtlib.MenhirInterpreter.loop_handle
      (fun x -> x)
      (fun _ ->
         let loc = ParseLocation.of_lexbuf buf in
         Input.consume_line buf;
         raise (Parse_error (loc, "Parsing error"))
      ) supplier
  in
  let rec aux () =
     match !curr with
     | x :: r -> curr := r; Some (translate x)
     | [] ->
       begin match loop (Parsesmtlib.Incremental.input buf.Lexing.lex_curr_p) with
       | None -> None
       | Some l -> curr := l; aux ()
       end
  in
  aux

