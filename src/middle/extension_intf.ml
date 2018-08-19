(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** {2 Extension interface} *)

module type S = sig
  (** This defines the external interface of an extension combinator. *)

  type ext
  (** The type of extensions *)

  type id = private int
  (** The type of identifiers asosciated to extensions. *)

  type t = {
    id : id;
    prio : int;
    name : string;
    descr : string;
    options : unit Cmdliner.Term.t;

    ext : ext;
  }
  (** Wrapper around extensions to register priority, etc... *)

  val get_res : unit -> ext
  (** Get the current merged extension. *)

  val register :
    string -> ?descr:string -> ?prio:int ->
    ?options:(unit Cmdliner.Term.t) -> ext -> unit
  (* Register a new extension. *)

  val activate : string -> unit
  val deactivate : string -> unit
  (** Activate and deactivate an extension using their name. *)

  val set_ext : string -> unit
  (** Convenience function for setting extensions. The syntax is as follows:
      - [set_ext "+ext"] activates an extensions
      - [set_ext "-ext"] deactivates an extensions
      - [set_ext "ext"] toggles an extensions (i.e
          activate it if was deactivated, and deactivate it if it was activated).
  *)

  val set_exts : string -> unit
  (** Same as [set_ext] but accepts a comma-separated list of extensions to set .*)

  val is_active : t -> bool
  (** Is the given extension active ? *)

  val active : unit -> string list
  (** Log the active extension using the given logger. *)

  val get : id -> t
  (** Get and extension by its id. *)

  val find : string -> t
  (** Find an extension using its name. *)

  val list : unit -> t list
  (** The list of all registered extensions. *)

  val ext_doc : unit -> Cmdliner.Manpage.block list
  (** Generate documentation for the extensions. *)

  val opts : unit -> unit Cmdliner.Term.t
  (** Generate the term for extensions options. *)

end
