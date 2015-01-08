
(** Convenience functions *)

let rec print_list f sep fmt = function
  | [] -> ()
  | [x] -> Format.fprintf fmt "%a%s" f x sep
  | x :: r ->
    Format.fprintf fmt "%a%s" f x sep;
    print_list f sep fmt r

let rec print_list_pre f sep fmt = function
  | [] -> ()
  | x :: r ->
    Format.fprintf fmt "%s%a" sep f x;
    print_list_pre f sep fmt r
(** Printing utilities *)

let list_const n c =
  let rec aux acc n c =
    if n <= 0 then acc
    else aux (c :: acc) (n - 1) c
  in
  aux [] n c
(** Builds the list with n times the value c. Tail-rec. *)
