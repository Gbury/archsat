
(* Wrapper for hashconsing *)
let find_wrap tbl key f =
    try Hashtbl.find tbl key
    with Not_found ->
        let res = f () in
        Hashtbl.add tbl key res;
        res

(* Builds the list with n times the value c. Tail-rec. *)
let list_const n c =
    let rec aux acc n c =
        if n <= 0 then acc
        else aux (c :: acc) (n - 1) c
    in
    aux [] n c
