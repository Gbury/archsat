
module type S = sig

  type ext
  type id = private int

  type t = {
    id : id;
    prio : int;
    name : string;
    descr : string;
    options : unit Cmdliner.Term.t;

    ext : ext;
  }

  val get_res : unit -> ext

  (* Registering and setting extensions *)
  val register :
    string -> ?descr:string -> ?prio:int ->
    ?options:(unit Cmdliner.Term.t) -> ext -> unit

  val activate : string -> unit
  val deactivate : string -> unit

  val set_ext : string -> unit
  val set_exts : string -> unit

  (* Active extensions *)
  val is_active : t -> bool
  val log_active : int -> unit

  (* Acces to extensions *)
  val get : id -> t
  val find : string -> t
  val list : unit -> t list

  (* Cmdliner doc & options *)
  val add_opts : 'a Cmdliner.Term.t -> 'a Cmdliner.Term.t
  val ext_doc : unit -> Cmdliner.Manpage.block list
end
