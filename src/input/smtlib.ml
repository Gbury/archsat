
exception Parse_error of ParseLocation.t * string

let translate c = c

(* raise a readable parse error *)
let _raise_error msg lexbuf =
  let loc = ParseLocation.of_lexbuf lexbuf in
  raise (Parse_error (loc, msg))

let parse_file f =
  let input = open_in f in
  let buf = Lexing.from_channel input in
  ParseLocation.set_file buf f;
  let commands =
    try
      Parsesmtlib.commands Lexsmtlib.token buf
    with Parsesmtlib.Error -> _raise_error "Parse error" buf
  in
  let res = Queue.create () in
  List.iter (fun c -> Queue.push (translate c) res) commands;
  res

