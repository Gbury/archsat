
(** Gloabl options for the prover. *)

type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

(** Type for input formats. *)

type output =
  | Standard
  | Dot

(** Type for output formats. *)

type model =
  | NoModel
  | Simple
  | Full

(** Type for choosing *)

type copts = {
    (** Input/Output option *)
    formatter : Format.formatter;
    input_file : string;
    input_format : input;
    output_format : output;

    (** Proving options *)
    proof : bool;
    solve : bool;
    extensions : string list;

    (** Printing options *)
    print_proof : out_channel option;
    print_model : model;

    (** Limits *)
    time_limit : float;
    size_limit : float;
}

(** Common options for theorem proving. *)

val clean : copts -> unit
(** Closes open file descriptors (namely the out_channel of print_proof). *)

val ext_sect : string
val copts_sect : string
(** Section names for options in cmdliner. *)

val help_secs : Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list
(** Given documentation for extensions, returns a documentation for the tool. *)

val copts_t : unit -> copts Cmdliner.Term.t
(** A term to evaluate common options from the command line. *)
