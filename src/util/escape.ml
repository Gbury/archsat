
let section = Section.make "escape"

(* Wrapper around polymorphic identifiers *)
(* ************************************************************************ *)

module Any = struct

  type t =
    | Id : _ Expr.id -> t
    | Dolmen : Dolmen.Id.t -> t

  let hash = function
    | Id id -> Expr.Id.hash id
    | Dolmen id -> Dolmen.Id.hash id

  let equal a b =
    match a, b with
    | Id x, Id y -> Expr.(x.index = y.index)
    | Dolmen x, Dolmen y -> Dolmen.Id.equal x y
    | _ -> false

  let print fmt = function
    | Id id -> Expr.Id.print fmt id
    | Dolmen id -> Dolmen.Id.print fmt id

end

module H = Hashtbl.Make(Any)

(* Printing wrappers for escapped sequences *)
(* ************************************************************************ *)

type status =
  | Same    (* No changes to the identifiers name *)
  | Escaped (* Identifiers has been escaped *)
  | Renamed (* Identifier has been renamed due to a conflict
               with another escaped or renamed identifier *)

type name =
  | Exact of string   (** The given name is to be printed exactly as is *)
  | Normal of string  (** The given name should be escaped/renamed if necessary *)

type t = {
  lang   : string;
  name   : Any.t -> name;     (* function for identifier name *)
  escape : string -> string;  (* escape function, ideally idempotent *)
  rename : string -> string;  (* renaming function, should have no fixpoint *)
  table  : (status * string) H.t;
  names  : (string, Any.t) Hashtbl.t;
}

let mk ~lang ~name ~escape ~rename = {
  lang; name;
  escape; rename;
  table = H.create 1013;
  names = Hashtbl.create 1013;
}


let pp_assign fmt (any, status, name) =
  Format.fprintf fmt "@[<hov>%a@ %s@ %s@]"
    Any.print any
    (match status with
     | Same -> "->"
     | Escaped -> "~>"
     | Renamed -> "~~>")
    name

(* Adding escapped sequences *)
(* ************************************************************************ *)

let rec add ?(fragile=false) t any status name =
  match Hashtbl.find t.names name with
  | exception Not_found ->
    add_success t any status name
  | r ->
    assert (not (Any.equal any r));
    if status = Same then begin
      match H.find t.table r with
      (** Two ids have the same name, we trust the developpers
          that this is intended *)
      | (Same, s) ->
        assert (s = name);
        add_success t any status name
      (** The escaped id collided with another escaped/renamed id,
          this is a potentially dangerous situation. *)
      | _ ->
        add_failure ~fragile t any status name r
    end else
      add_failure ~fragile t any status name r

and add_success t any status name =
  (* Util.debug ~section "Adding %a" pp_assign (any, status, name); *)
  let () = H.add t.table any (status, name) in
  let () = Hashtbl.add t.names name any in
  name

and add_failure ~fragile t any status name r =
  let conflict_st, conflict_name = H.find t.table r in
  let log = if fragile then Util.error else Util.warn in
  log ~section "Escaping %a,@ conficted with@ %a"
    pp_assign (any, status, name) pp_assign (r, conflict_st, conflict_name);
  let new_name = t.rename name in
  assert (new_name <> name);
  add t any Renamed new_name

let escape t any =
  match H.find t.table any with
  | (_, s) -> s
  | exception Not_found ->
    let fragile, status, new_name =
      match t.name any with
      | Exact name ->
        true, Same, name
      | Normal name ->
        let s = t.escape name in
        let status = if (s = name) then Same else Escaped in
        false, status, s
    in
    add ~fragile t any status new_name

(* Convenience functions *)
(* ************************************************************************ *)

let id t fmt id =
  Format.fprintf fmt "%s" (escape t (Any.Id id))

let dolmen t fmt id =
  Format.fprintf fmt "%s" (escape t (Any.Dolmen id))

let rec tagged_name_aux id = function
  | [] -> Normal (id.Expr.id_name)
  | tag :: r ->
    begin match Expr.Id.get_tag id tag with
      | Some s -> Exact s
      | None -> tagged_name_aux id r
    end

let tagged_name ?(tags=[Expr.Print.name]) = function
  | Any.Dolmen id ->
    Normal (Dolmen.Id.full_name id)
  | Any.Id id -> tagged_name_aux id tags

(* Unicode wrapper *)
(* ************************************************************************ *)

let encode e c =
  match Uutf.encode e c with
  | `Ok -> ()
  | `Partial ->
    (* should only happen with manual sources according to the doc,
       so it is safe to assume it doesn't happen *)
    assert false

let encode_char e c = encode e (`Uchar c)

let umap f s =
  let encoding = `UTF_8 in
  let b = Buffer.create (String.length s) in
  let d = Uutf.decoder ~encoding (`String s) in
  let e = Uutf.encoder encoding (`Buffer b) in
  let rec aux () =
    match Uutf.decode d with
    | `End ->
      let () = encode e `End in
      Buffer.contents b
    | `Await ->
      let () = encode e `Await in
      aux ()
    | `Uchar c ->
      let pos = Uutf.decoder_count d in
      let () = List.iter (encode_char e) (f pos (Some c)) in
      aux ()
    | `Malformed _ ->
      let pos = Uutf.decoder_count d in
      let () = List.iter (encode_char e) (f pos None) in
      aux ()
  in
  aux ()


(* Print an Uchar *)
(* ************************************************************************ *)

let pp_uchar fmt c =
  let b = Buffer.create 5 in
  let () = Uutf.Buffer.add_utf_8 b c in
  let s = Buffer.contents b in
  Format.fprintf fmt "%s" s


(* Renaming function *)
(* ************************************************************************ *)

let get_num ~sep s =
  let rec aux acc mult i =
    if i < 0 then s, 0
    else match s.[i] with
      | ('0' .. '9') as c ->
        let j = int_of_char c - 48 in
        aux (acc + j * mult) (mult * 10) (i - 1)
      | c when c = sep ->
        if i = 0 then s, 0 (* no base name found *)
        else String.sub s 0 i, acc
      | _ -> s, 0
  in
  aux 0 1 (String.length s - 1)

let rename ~sep s =
  let base, n = get_num ~sep s in
  Format.sprintf "%s%c%d" base sep (n + 1)


