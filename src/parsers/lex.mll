{
  type token =
    | EOF
    | CHAR of char
}

rule token = parse
  | eof { EOF }
  | _ as c { CHAR c }
