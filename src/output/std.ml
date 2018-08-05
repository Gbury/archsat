
(* Some helper functions *)
(* ************************************************************************ *)

let prelude opt =
  match Options.(opt.input.format) with
  | None -> ""
  | Some l -> Format.asprintf "(%s)# @?" (In.string_of_language l)

let prelude_space opt =
  String.make (String.length (prelude opt) - 8) ' '

(* Location functions *)
(* ************************************************************************ *)

let default_loc opt = Dolmen.ParseLocation.mk
    (Options.input_to_string Options.(opt.input.file)) 0 0 0 0

let get_loc opt loc = CCOpt.get_or ~default:(default_loc opt) loc

(* Output functions *)
(* ************************************************************************ *)

let print_status opt fmt status =
  Format.fprintf fmt "%s (%a)" status Mtime.Span.pp (Mtime_clock.elapsed ())

let print_sat fmt opt = print_status opt fmt "Sat"
let print_unsat fmt opt = print_status opt fmt "Unsat"
let print_unknown fmt opt = print_status opt fmt "Unknown"

let print_exn opt fmt = function

  (** User interrupt *)
  | Options.Sigint ->
    print_status opt fmt "User interrupt"

  (** Size and time limits *)
  | Options.Out_of_time ->
    print_status opt fmt "Timeout"
  | Options.Out_of_space ->
    print_status opt fmt "Out of space"

  (** File not found *)
  | Options.File_not_found f ->
    Format.fprintf fmt "File not found: '%s'" f

  (** Could not recognize file extension *)
  | In.Extension_not_found ext ->
    if ext = "" then
      Format.fprintf fmt
        ("@[<hov>Given file has no file extension, cannot detect input format" ^^
         "@\nTry and specify an explicit input format using the -i option@]")
    else
      Format.fprintf fmt
        ("@[<hov>Could not find a supported input format with extension '%s'" ^^
         "@\nTry and specify an explicit input format using the -i option@]") ext

  (** Statement not implemented *)
  | Options.Stmt_not_implemented s ->
    let default_loc = Dolmen.ParseLocation.mk
        (Options.input_to_string Options.(opt.input.file)) 0 0 0 0 in
    let loc = CCOpt.get_or ~default:default_loc s.Dolmen.Statement.loc in
    Format.fprintf Format.std_formatter
      "%a: the following statement is not yet treated:@\n%a@."
      Dolmen.ParseLocation.fmt loc Dolmen.Statement.print s

  (** Parsing errors *)
  | Dolmen.ParseLocation.Uncaught (loc, exn) ->
    if Options.(opt.input.mode = Interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\n%s@."
      Dolmen.ParseLocation.fmt loc (Printexc.to_string exn)
  | Dolmen.ParseLocation.Lexing_error (loc, msg) ->
    if Options.(opt.input.mode = Interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\nLexing error: invalid character '%s'@."
      Dolmen.ParseLocation.fmt loc msg
  | Dolmen.ParseLocation.Syntax_error (loc, msg) ->
    if Options.(opt.input.mode = Interactive) then
      Format.fprintf Format.std_formatter "%s%a@\n"
        (if Dolmen.ParseLocation.(loc.start_line = 1) then prelude_space opt else "")
        Dolmen.ParseLocation.fmt_hint loc;
    Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc
      (match msg with "" -> "Syntax error" | x -> x)

  (** Typing errors *)
  | Type.Typing_error (msg, env, t) ->
    let loc = get_loc opt t.Dolmen.Term.loc in
    Format.fprintf Format.std_formatter "@[<hv>While typing:@ @[<hov>%a@]@]@." Dolmen.Term.print t;
    Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc msg

  (** Extension not found *)
  | Extension.Extension_not_found (sect, ext, l) ->
    Format.fprintf Format.std_formatter
      "Extension '%s/%s' not found.@ Available extensions are :@\n%a@."
      sect ext (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) l

  (** Proofs errors *)
  | Synth.Cannot_find ty ->
    Format.fprintf Format.std_formatter
      "@[<hv>Couldn't find a way to generate a term of type@ %a@ which is necessary for proof generation@]"
      Expr.Ty.print ty;
  | Prove.Hypothesis_name_conflict ((h, hloc), (h', hloc')) ->
    let loc = get_loc opt hloc in
    let loc' = get_loc opt hloc' in
    Format.fprintf Format.std_formatter
      "@[<v>Two hypothesis have the same name:@ %a: defines %a@ %a: defines %a@]"
      Dolmen.ParseLocation.fmt loc Expr.Id.print h
      Dolmen.ParseLocation.fmt loc' Expr.Id.print h'

  (** Internal errors. This is BAD, it should *not* happen *)
  | Dispatcher.Bad_assertion msg ->
    Format.fprintf Format.std_formatter "%s@." msg
  | Dispatcher.Not_assigned t ->
    Format.fprintf Format.std_formatter
      "The following term's assignment couldn't be found, this is an error:@\n%a" Expr.Term.print t

  | Expr.Type_mismatch (t, ty1, ty2) ->
    Format.fprintf Format.std_formatter
      "Term@ %a@ has type %a@ but an expression of type@ %a@ was expected@."
      Expr.Print.term t Expr.Print.ty ty1 Expr.Print.ty ty2
  | Term.Function_expected t ->
    Format.fprintf Format.std_formatter
      "@[<hv>Proof term@ %a :@ %a@ was expected to be a function@]"
      Term.print t Term.print t.Term.ty
  | Term.Type_mismatch (t, ty) ->
    Format.fprintf Format.std_formatter
      "Proof term@ %a@ was expected to have type@ %a@ but has type@ %a"
      Term.print t Term.print ty Term.print Term.(t.ty)

  (** Generic catch *)
  | exn ->
    Format.fprintf fmt "%s@\n%s@."
      "Uncaught exception:" (Printexc.to_string exn)






