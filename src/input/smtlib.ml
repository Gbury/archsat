
(*
let log_section = Util.Section.make "smtlib"
let log i fmt = Util.debug ~section:log_section i fmt
*)

let translate c = c

let parse_file f =
    let input = open_in f in
    let buf = Lexing.from_channel input in
    ParseLocation.set_file buf f;
    let commands = Parsesmtlib.commands Lexsmtlib.token buf in
    let res = Queue.create () in
    List.iter (fun c -> Queue.push (translate c) res) commands;
    res

