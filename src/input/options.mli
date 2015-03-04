
type model =
  | None
  | Simple
  | Full

type copts = {
    (* Input/Output option *)
    formatter : Format.formatter;
    input_file : string;
    input_format : Io.input;
    output_format : Io.output;

    (* Proving options *)
    proof : bool;
    solve : bool;
    extensions : string list;

    (* Printing options *)
    print_proof : bool;
    print_model : model;

    (* Limits *)
    time_limit : float;
    size_limit : float;
}

val copts_sect : string
val copts_t : copts Cmdliner.Term.t


