
exception Abort of string * string
exception Extension_not_found of string * string* string list

module type K = sig
  type t
  val neutral : t
  val merge : high:t -> low:t -> t
  val section : Util.Section.t
end

module type S = Extension_intf.S

module Make(E: K) : S with type ext = E.t = struct

  let log_name = Util.Section.short_name E.section
  let log i fmt = Util.debug ~section:E.section i fmt

  (* Type definitions *)
  type id = int
  type ext = E.t

  type t = {
    id :id;
    prio : int;
    name : string;
    descr : string;
    options : unit Cmdliner.Term.t;

    ext : E.t;
  }

  (* Internal state *)
  let actual = ref E.neutral
  let exts = CCVector.create ()
  let active = ref []

  (* Get the current extension result *)
  let get_res () = !actual

  (* Get extensions *)
  let _not_found ext_name =
    raise (Extension_not_found (
        log_name, ext_name, List.map (fun r -> r.name) (CCVector.to_list exts)))

  let get id = CCVector.get exts id

  let find name = match CCVector.find (fun r -> r.name = name) exts with
    | Some x -> x
    | None -> _not_found name

  (* Register extensions *)
  let register name
      ?(descr="think hard !") ?(prio=10)
      ?(options=(Cmdliner.Term.pure ())) ext =
    assert (not (CCVector.exists (fun r -> r.name = name) exts));
    if prio < 0 then log 0 "WARNING: %s - extensions should have positive priority" name;
    let id = CCVector.length exts in
    CCVector.push exts { id; prio; name; descr; options; ext }

  (* Merge extensions *)
  let merge high low = E.merge ~high ~low

  let refresh () =
    actual := List.fold_left merge E.neutral (List.map (fun t -> t.ext) !active)

  (* Activate/deactivate extensions *)
  let activate ext =
    let aux r = r.name = ext in
    try
      let r = CCVector.find_exn aux exts in
      if not (List.exists aux !active) then begin
        active := List.merge (fun r r' -> compare r'.prio r.prio) [r] !active;
        refresh ()
      end else
        log 0 "WARNING: Extension %s already activated" ext
    with Not_found -> _not_found ext

  let deactivate ext =
    let aux r = r.name = ext in
    try
      if not (CCVector.exists aux exts) then _not_found ext;
      let l1, l2 = List.partition aux !active in
      begin match l1 with
        | [] -> log 0 "WARNING: Extension %s already deactivated" ext
        | [r] ->
          active := l2;
          refresh ()
        | _ -> assert false
      end
    with Not_found -> _not_found ext

  let set_ext s =
    if s <> "" then match s.[0] with
      | '-' -> deactivate (String.sub s 1 (String.length s - 1))
      | '+' -> activate (String.sub s 1 (String.length s - 1))
      | _ -> activate s

  let set_exts s =
    List.iter set_ext
      (List.map (fun (s, i, l) -> String.sub s i l) (CCString.Split.list_ ~by:"," s))

  (* Active extensions *)
  let is_active t =
    List.exists (fun r -> r.name = t.name) !active

  let log_active lvl =
    log lvl "active: %a" CCPrint.(list string) (List.map (fun r -> r.name) !active)


  (* Info about extensions *)
  let list () = CCVector.to_list exts

  let doc_of_ext r =
    `I (Printf.sprintf "$(b,%.2d - %s)" r.prio r.name, r.descr)

  let ext_doc () =
    List.map doc_of_ext @@
    List.sort (fun r r' -> match compare r'.prio r.prio with
        | 0 -> compare r.name r'.name | x -> x) @@ list ()

  let add_opts t =
    let combine = Cmdliner.Term.pure (fun x () -> x) in
    CCVector.fold (fun t r ->
      Cmdliner.Term.(combine $ t $ r.options)) t exts

end
