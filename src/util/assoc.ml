
module type S = sig

    type key
    type 'a t
    type level

    val create : int -> 'a t

    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a

    val fold : 'a t -> (key -> 'a -> 'b -> 'b) -> 'b -> 'b

    val dummy_level : level
    val current_level : 'a t -> level
    val backtrack : 'a t -> level -> unit
end

module Make(T : Hashtbl.HashedType) = struct

    module H = Hashtbl.Make(T)

    type key = T.t

    type 'a task =
        | Add of key * 'a
        | Remove of key

    type 'a t = {
        table : 'a H.t;
        mutable count : int;
        mutable undo : 'a task list;
    }

    type level = int

    let dummy_level = -1

    (* Backtrack engine *)
    let current_level h = h.count

    let execute h = function
        | Add (key, value) -> H.add h.table key value
        | Remove key -> H.remove h.table key

    let rec undo h n = function
        | l when n <= 0 -> h.undo <- l
        | t :: r -> execute h t; undo h (n - 1) r
        | [] -> assert false

    let backtrack h level =
        assert (level >= 0);
        if level <= h.count then begin
            undo h (h.count - level) h.undo;
            h.count <- level;
            assert (h.count = List.length h.undo)
        end

    (* Standard operations *)
    let create n = {
        table = H.create n;
        count = 0;
        undo = [];
    }

    let add_task h t =
        h.undo <- t :: h.undo;
        h.count <- h.count + 1

    let find h = H.find h.table

    let add h key value =
        H.add h.table key value;
        add_task h (Remove key)

    let remove h key =
        let value = find h key in
        H.remove h.table key;
        add_task h (Add (key, value))

    let fold h f acc = H.fold f h.table acc

end
