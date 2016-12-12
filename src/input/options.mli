
(** Global options for the prover. *)

exception Sigint
exception Out_of_time
exception Out_of_space
(** Some exceptions *)

val misc_section : Util.Section.t

type output =
  | Standard
  | SZS
(** Type for choosing model output *)

type profile_options = {
  enabled : bool;
  max_depth : int option;
  sections : Util.Section.t list;
  raw_data : Format.formatter option;
  print_stats : bool;
}

type proof_options = {
  active      : bool;
  dot         : Format.formatter option;
  unsat_core  : Format.formatter option;
}

type copts = {

  (* Input/Output *)
  out           : Format.formatter;
  input_dir     : string;
  input_file    : [ `Stdin | `File of string];

  (* Input/Output options *)
  output_format : output;
  input_format  : In.language option;
  interactive   : bool;

  (* Solving options *)
  solve   : bool;
  addons  : string list;
  plugins : string list;

  (* Proof options *)
  proof   : proof_options;

  (* Printing options *)
  model_out : Format.formatter option;

  (* Time/Memory options *)
  time_limit  : float;
  size_limit  : float;
  profile     : profile_options;
}
(** Common options for theorem proving. *)

val input_to_string : [ `Stdin | `File of string ] -> string
(** String representation of inut mode. *)

val log_opts : copts -> unit
(** Prints a summary of options *)

val ext_sect : string
val copts_sect : string
val proof_sect : string
(** Section names for options in cmdliner. *)

val help_secs : Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list -> Cmdliner.Manpage.block list
(** Given documentation for extensions, returns a documentation for the tool. *)

val copts_t : unit -> copts Cmdliner.Term.t
(** A term to evaluate common options from the command line. *)

