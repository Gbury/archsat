
type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

type output =
  | Standard
  | Dot

type model =
  | NoModel
  | Simple
  | Full

type copts = {
    (* Input/Output option *)
    formatter : Format.formatter;
    input_file : string;
    input_format : input;
    output_format : output;

    (* Proving options *)
    proof : bool;
    solve : bool;
    extensions : string list;

    (* Printing options *)
    print_proof : out_channel option;
    print_model : model;

    (* Limits *)
    time_limit : float;
    size_limit : float;
}

val clean : copts -> unit

val copts_sect : string
val ext_sect : string
val help_secs : Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list

val copts_t : unit -> copts Cmdliner.Term.t

