(*
   This module represents positions in
   types, terms and formulas.
*)

(* Misc *)
(* ************************************************************************ *)

exception Invalid

let rec nth n = function
  | [] -> raise Invalid
  | x :: _ when n <= 0 -> x
  | _ :: r -> nth (n - 1) r

(* Signature for position modules *)
(* ************************************************************************ *)

module type S = sig
  type t
  type expr

  val root : t
  val arg : int -> t -> t

  val compare : t -> t -> int

  val apply : t -> expr -> expr
  val substitute : t -> by:expr -> expr -> expr
  val fold : ('a -> t -> expr -> 'a) -> 'a -> expr -> 'a
  val find_map : (t -> expr -> 'a option) -> expr -> 'a option
end

(* Positions for Types *)
(* ************************************************************************ *)

module Ty : S with type expr = Expr.ty = struct

  type t =
    | Here
    | Arg of int * t

  type expr = Expr.ty

  let root = Here

  let arg i t = Arg (i, t)

  let compare = compare

  let rec apply p t = match p, t with
    | Here, _ -> t
    | Arg (k, p'), { Expr.ty = Expr.TyApp(_, l) } ->
      apply p' (nth k l)
    | _ -> raise Invalid

  let rec substitute p ~by:u t =
    match p, t with
    | Here, _ -> u
    | Arg (k, p'), { Expr.ty = Expr.TyApp(f, l) } ->
      Expr.Ty.apply ~status:t.Expr.ty_status f
        (List.mapi (fun i v -> if i = k then substitute p' ~by:u v else v) l)
    | _ -> raise Invalid

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.ty = Expr.TyApp (_, l) } ->
      CCList.Idx.foldi (fun acc i t ->
          fold_aux f acc (fun p -> cur_pos (Arg(i, p))) t) acc' l
    | _ -> acc'

  let fold f acc t = fold_aux f acc (fun x -> x) t

  let rec find_map_aux f cur_pos t =
    match f (cur_pos Here) t with
    | Some res -> Some res
    | None ->
      begin match t with
        | { Expr.ty = Expr.TyApp (_, l) } ->
          CCList.find_mapi (fun i t -> find_map_aux f (fun p -> cur_pos (Arg(i, p))) t) l
        | _ -> None
      end

  let find_map f t = find_map_aux f (fun x -> x) t

end

(* Positions for Terms *)
(* ************************************************************************ *)

module Term : S with type expr = Expr.term = struct

  type t =
    | Here
    | Arg of int * t

  type expr = Expr.term

  let root = Here

  let arg i t = Arg (i, t)

  let compare = compare

  let rec apply p t = match p, t with
    | Here, _ -> t
    | Arg (k, p'), { Expr.term = Expr.App(_, _, l) } ->
      apply p' (nth k l)
    | _ -> raise Invalid

  let rec substitute p ~by:u t =
    match p, t with
    | Here, _ -> u
    | Arg (k, p'), { Expr.term = Expr.App(f, ty_args, l) } ->
      Expr.Term.apply ~status:t.Expr.t_status f ty_args
        (List.mapi (fun i v -> if i = k then substitute p' ~by:u v else v) l)
    | _ -> raise Invalid

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.term = Expr.App (_, _, l) } ->
      CCList.Idx.foldi (fun acc i t ->
          fold_aux f acc (fun p -> cur_pos (Arg(i, p))) t) acc' l
    | _ -> acc'

  let fold f acc t = fold_aux f acc (fun x -> x) t

  let rec find_map_aux f cur_pos t =
    match f (cur_pos Here) t with
    | Some res -> Some res
    | None ->
      begin match t with
        | { Expr.term = Expr.App (_, _, l) } ->
          CCList.find_mapi (fun i t -> find_map_aux f (fun p -> cur_pos (Arg(i, p))) t) l
        | _ -> None
      end

  let find_map f t = find_map_aux f (fun x -> x) t
end

