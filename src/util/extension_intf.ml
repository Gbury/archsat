
module type S = sig
  type id = private int
  type ext
  type opt = Options.copts

  type t = {
    id :id;
    prio : int;
    name : string;
    descr : string;
    options : opt Cmdliner.Term.t -> opt Cmdliner.Term.t;

    ext : ext;
  }

  val get_res : unit -> ext

  (* Registering and setting extensions *)
  val register : string -> ?descr:string -> ?prio:int ->
    ?options:(opt Cmdliner.Term.t -> opt Cmdliner.Term.t) -> ext -> id

  val activate : string -> unit
  val deactivate : string -> unit

  val set_ext : string -> unit
  val set_exts : string -> unit

  (* Logging *)
  val log_active : int -> unit

  (* Acces to extensions *)
  val get : id -> t
  val find : string -> t
  val list : unit -> t list

  (* Cmdliner doc & options *)
  val add_opts : opt Cmdliner.Term.t -> opt Cmdliner.Term.t
  val ext_doc : unit -> Cmdliner.Manpage.block list
end
