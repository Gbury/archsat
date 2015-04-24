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
  val compare : t -> t -> int

  val apply : t -> expr -> expr
  val substitute : t -> expr -> expr -> expr
  val fold : ('a -> t -> expr -> 'a) -> 'a -> expr -> 'a
end

(* Positions for Types *)
(* ************************************************************************ *)

module Ty : S with type expr = Expr.ty = struct

  type t =
    | Here
    | Arg of int * t

  type expr = Expr.ty

  let root = Here
  let compare = compare

  let rec apply p t = match p, t with
    | Here, _ -> t
    | Arg (k, p'), { Expr.ty = Expr.TyApp(_, l) } ->
      apply p' (nth k l)
    | _ -> raise Invalid

  let rec substitute p u t =
    match p, t with
    | Here, _ -> u
    | Arg (k, p'), { Expr.ty = Expr.TyApp(f, l) } ->
      Expr.type_app ~goalness:t.Expr.ty_goalness f
        (List.mapi (fun i v -> if i = k then substitute p' u v else v) l)
    | _ -> raise Invalid

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.ty = Expr.TyApp (_, l) } ->
      CCList.Idx.foldi (fun acc i t ->
          fold_aux f acc (fun p -> cur_pos (Arg(i, p))) t) acc' l
    | _ -> acc'

  let fold f acc t = fold_aux f acc (fun x -> x) t
end

(* Positions for Terms *)
(* ************************************************************************ *)

module Term : S with type expr = Expr.term = struct

  type t =
    | Here
    | Arg of int * t

  type expr = Expr.term

  let root = Here
  let compare = compare

  let rec apply p t = match p, t with
    | Here, _ -> t
    | Arg (k, p'), { Expr.term = Expr.App(_, _, l) } ->
      apply p' (nth k l)
    | _ -> raise Invalid

  let rec substitute p u t =
    match p, t with
    | Here, _ -> u
    | Arg (k, p'), { Expr.term = Expr.App(f, ty_args, l) } ->
      Expr.term_app ~goalness:t.Expr.t_goalness f ty_args
        (List.mapi (fun i v -> if i = k then substitute p' u v else v) l)
    | _ -> raise Invalid

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.term = Expr.App (_, _, l) } ->
      CCList.Idx.foldi (fun acc i t ->
          fold_aux f acc (fun p -> cur_pos (Arg(i, p))) t) acc' l
    | _ -> acc'

  let fold f acc t = fold_aux f acc (fun x -> x) t
end

