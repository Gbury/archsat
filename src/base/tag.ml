(*
   Arbitrary tags for expressions.
   Uses a mixed map (see containers.data.CCMixmap)
*)

(* Type definitions *)
(* ************************************************************************ *)

module M = CCMixmap.Make(struct
    type t = int
    let compare (a: int) (b: int) =
      Pervasives.compare a b
  end)

type map = M.t

type 'a t = {
  id : int;
  inj : 'a CCMixmap.injection;
}

let mk_key id = { id; inj = CCMixmap.create_inj (); }

let max_id = ref 0

let new_tag () =
  incr max_id;
  mk_key !max_id

let empty = M.empty

let get m k = M.get ~inj:k.inj m k.id
let add m k v = M.add ~inj:k.inj m k.id v

