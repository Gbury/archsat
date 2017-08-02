
let section = Section.make "escape"

(* Wrapper around polymorphic identifiers *)
(* ************************************************************************ *)

module Any = struct

  type t = Id : _ Expr.id -> t

  let hash (Id id) = Expr.Id.hash id

  let equal (Id x) (Id y) = Expr.(x.index = y.index)

end

module H = Hashtbl.Make(Any)

(* Printing wrappers for escapped sequences *)
(* ************************************************************************ *)

type status =
  | Same    (* No changes to the identifiers name *)
  | Escaped (* Identifiers has been escaped *)
  | Renamed (* Identifier has been renamed due to a conflict
               with another escaped or renamed identifier *)

type t = {
  lang   : string;
  name   : Any.t -> string; (* function for identifier name *)
  escape : string -> string; (* escape function, ideally idempotent *)
  rename : string -> string; (* renaming function, should have no fixpoint *)
  table  : (status * string) H.t;
  names  : (string, Any.t) Hashtbl.t;
}

let mk ~lang ~name ~escape ~rename = {
  lang; name;
  escape; rename;
  table = H.create 1013;
  names = Hashtbl.create 1013;
}

let pp_assign fmt ((Any.Id id), status, name) =
  Format.fprintf fmt "@[<hov>%a@ %s@ %s@]"
    Expr.Print.id id
    (match status with
     | Same -> "->"
     | Escaped -> "~>"
     | Renamed -> "~~>")
    name

let rec add t any status name =
  match Hashtbl.find t.names name with
  | exception Not_found ->
    add_success t any status name
  | (Any.Id id) as r ->
    assert (not (Any.equal any r));
    if status = Same then begin
      match H.find t.table r with
      | (Same, s) when s = name ->
        add_success t any status name
      | _ ->
        add_failure t any status name r
    end else
      add_failure t any status name r

and add_success t any status name =
  Util.debug ~section "Adding %a" pp_assign (any, status, name);
  let () = H.add t.table any (status, name) in
  let () = Hashtbl.add t.names name any in
  name

and add_failure t any status name r =
  let conflict_st, conflict_name = H.find t.table r in
  Util.warn ~section "Escaping %a,@ conficted with@ %a"
    pp_assign (any, status, name) pp_assign (r, conflict_st, conflict_name);
  let new_name = t.rename name in
  assert (new_name <> name);
  add t any Renamed new_name

let escape t id =
  let any = Any.Id id in
  match H.find t.table any with
  | (_, s) -> s
  | exception Not_found ->
    let name = t.name any in
    let new_name = t.escape name in
    let status = if (new_name = name) then Same else Escaped in
    add t any status new_name

let print t fmt id =
  Format.fprintf fmt "%s" (escape t id)

let print_string t fmt s =
  Format.fprintf fmt "%s" (t.escape s)

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


(* Language-specific escapers *)
(* ************************************************************************ *)

let coq =
  let escape = umap (fun i -> function
      | None -> [ Uchar.of_char '_' ]
      | Some c ->
        let g = Uucp.Gc.general_category c in
        begin match g with
          | `Lu | `Ll | `Lt | `Lm | `Lo | `Sm -> [ c ]
          | `Nd when i = 1 -> [ c ]
          | _ -> [ Uchar.of_char '_' ]
        end) in
  mk ~lang:"coq" ~escape ~rename:(rename ~sep:'_')


