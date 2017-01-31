
(* Some helper functions *)
(* ************************************************************************ *)

let start = ref 0.

let set_start () = start := Util.get_total_time ()

let flush fmt () =
  Format.fprintf fmt "@."

let prelude opt =
  match Options.(opt.input.format) with
  | None -> ""
  | Some l -> Format.asprintf "(%s)# @?" (In.string_of_language l)

let prelude_space opt =
  String.make (String.length (prelude opt)) ' '

(* Output functions *)
(* ************************************************************************ *)

let print_status opt fmt status =
  Format.fprintf fmt "%s (%.3f)@." status (Util.get_total_time () -. !start)

let print_sat opt fmt = print_status opt fmt "Sat"
let print_unsat opt fmt = print_status opt fmt "Unsat"
let print_unknown opt fmt = print_status opt fmt "Unknown"

let print_exn opt fmt = function

  (** User interrupt *)
  | Options.Sigint ->
    Format.fprintf fmt "User interrupt@."

  (** Size and time limits *)
  | Options.Out_of_time ->
    print_status opt fmt "Timeout@."
  | Options.Out_of_space ->
    print_status opt fmt "Out of space@."

  (** Statement not implemented *)
  | Options.Stmt_not_implemented s ->
    let default_loc = Dolmen.ParseLocation.mk
        (Options.input_to_string Options.(opt.input.file)) 0 0 0 0 in
    let loc = CCOpt.get default_loc s.Dolmen.Statement.loc in
    Format.fprintf Format.std_formatter
      "%a: the following statement is not yet treated:@\n%a@."
      Dolmen.ParseLocation.fmt loc Dolmen.Statement.print s

  (** Parsing errors *)
  | Dolmen.ParseLocation.Uncaught (loc, exn) ->
    if Options.(opt.input.interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\n%s@."
      Dolmen.ParseLocation.fmt loc (Printexc.to_string exn)
  | Dolmen.ParseLocation.Lexing_error (loc, msg) ->
    if Options.(opt.input.interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\n%s@."
      Dolmen.ParseLocation.fmt loc
      (match msg with | "" -> "Lexing error: invalid character" | x -> x)
  | Dolmen.ParseLocation.Syntax_error (loc, msg) ->
    if Options.(opt.input.interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc
      (match msg with "" -> "Syntax error" | x -> x)

  (** Typing errors *)
  | Type.Typing_error (msg, t) ->
    let default_loc = Dolmen.ParseLocation.mk
        (Options.input_to_string Options.(opt.input.file)) 0 0 0 0 in
    let loc = CCOpt.get default_loc t.Dolmen.Term.loc in
    Format.fprintf Format.std_formatter "While typing %a@\n" Dolmen.Term.print t;
    Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc msg

  (** Extension not found *)
  | Extension.Extension_not_found (sect, ext, l) ->
    Format.fprintf Format.std_formatter
      "Extension '%s/%s' not found. Available extensions are :@\n%a@."
      sect ext (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) l

  (** Internal errors. Should not happen *)
  | Dispatcher.Bad_assertion msg ->
    Format.fprintf Format.std_formatter "%s@." msg
  | Expr.Type_mismatch (t, ty1, ty2) ->
    Format.fprintf Format.std_formatter
      "Term %a has type %a but an expression of type %a was expected@."
      Expr.Print.term t Expr.Print.ty ty1 Expr.Print.ty ty2

  (** Generic catch *)
  | exn ->
    Format.fprintf fmt "%a%s@."
      (print_status opt) "Uncaught exception" (Printexc.to_string exn)






