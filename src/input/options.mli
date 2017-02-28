
(** Global options for the prover. *)

exception Sigint
exception Out_of_time
exception Out_of_space
exception File_not_found of string
exception Stmt_not_implemented of Dolmen.Statement.t

(** Some exceptions *)

val misc_section : Section.t

type input = In.language
(* Type alias for input languages *)

type output =
  | Standard
  | SZS
(** Type for output format *)

type mode =
  | Debug
  | Regular
  | Interactive
(** Type for modes of running. *)

type input_options = {
  mode    : mode;
  format  : input option;
  dir     : string;
  file    : [ `Stdin | `File of string];
}

type output_options = {
  format  : output;
  fmt     : Format.formatter;
}

type typing_options = {
  explain : [ `No | `Yes | `Full ];
}

type profile_options = {
  enabled : bool;
  max_depth : int option;
  sections : Section.t list;
  raw_data : Format.formatter option;
  print_stats : bool;
}

type proof_options = {
  active      : bool;
  dot         : Format.formatter option;
  unsat_core  : Format.formatter option;
}

type model_options = {
  active      : bool;
  assign      : Format.formatter option;
}

type opts = {

  (* Input&output options *)
  input   : input_options;
  output  : output_options;

  (* Typing options *)
  typing  : typing_options;

  (* Proof&model options *)
  proof   : proof_options;
  model   : model_options;

  (* Solving options *)
  solve   : bool;
  addons  : string list;
  plugins : string list;

  (* Time/Memory options *)
  time_limit  : float;
  size_limit  : float;
  profile     : profile_options;
}
(** Common options for theorem proving. *)

val input_to_string : [ `Stdin | `File of string ] -> string
(** String representation of inut mode. *)

val log_opts : opts -> unit
(** Prints a summary of options *)

val ext_sect : string
val copts_sect : string
val proof_sect : string
val model_sect : string
(** Section names for options in cmdliner. *)

val help_secs :
  Cmdliner.Manpage.block list ->
  Cmdliner.Manpage.block list ->
  Cmdliner.Manpage.block list
(** Given documentation for addons, then extensions,
    returns a documentation for the tool. *)

val copts_t : unit -> opts Cmdliner.Term.t
(** A term to evaluate common options from the command line. *)

