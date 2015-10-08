
(** Gloabl options for the prover. *)

val misc_section : Util.Section.t

type input =
  | Auto
  | Dimacs
  | Tptp
  | Smtlib

(** Type for input formats. *)

type output =
  | Standard
  | SZS

(** Type for choosing model output *)

type profile_options = {
  enabled : bool;
  max_depth : int option;
  sections : Util.Section.t list;
  raw_data : Format.formatter;
  print_stats : bool;
}

type copts = {
  (* Input/Output option *)
  out : Format.formatter;
  input_file : string;
  input_format : input;
  output_format : output;

  (* Proving options *)
  solve : bool;
  proof : bool;
  addons : string list;
  plugins : string list;

  (* Printing options *)
  dot_proof : Format.formatter;
  model_out : Format.formatter;

  (* Time/Memory options *)
  profile : profile_options;
  time_limit : float;
  size_limit : float;
}


(** Common options for theorem proving. *)

val log_opts : copts -> unit
(** Prints a summary of options *)

val clean : copts -> unit
(** Closes open file descriptors (namely the out_channel of print_proof). *)

val ext_sect : string
val copts_sect : string
(** Section names for options in cmdliner. *)

val help_secs : Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list
(** Given documentation for extensions, returns a documentation for the tool. *)

val copts_t : unit -> copts Cmdliner.Term.t
(** A term to evaluate common options from the command line. *)
