
(* Expand dolmen statements *)
(* ************************************************************************ *)

module S = Dolmen.Statement

exception File_not_found of string

let expand (opt, c) =
  match c with
  | { S.descr = S.Pack l } ->
    opt, `Gen (true, Gen.of_list l)
  (* TODO: filter the statements in the returned generator *)
  | { S.descr = S.Include f } ->
    let language = opt.Options.input_format in
    let dir = opt.Options.input_dir in
    begin
      match In.find ?language ~dir f with
      | None -> raise (File_not_found f)
      | Some file ->
        let l, gen = In.parse_input ?language (`File file) in
        let opt' = Options.{ opt with
                             input_format = Some l;
                             input_file = `File file;
                             interactive = false } in
        opt', (`Gen (false, gen))
    end
  | _ -> (opt, `Single c)





