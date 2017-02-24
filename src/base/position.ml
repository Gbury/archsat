(*
   This module represents positions in
   types, terms and formulas.
*)

(* Position type *)
(* ************************************************************************ *)

type t =
  | Here
  | Arg of int * t

(* Build positions *)
let root = Here

let arg i t = Arg (i, t)

let rec path = function
  | [] -> root
  | k :: r -> arg k (path r)


(* Comparison, equality, printing. *)
let equal = (=)
let compare = Pervasives.compare

let rec print fmt = function
  | Here -> Format.fprintf fmt "."
  | Arg (i, t) -> Format.fprintf fmt "%d-%a" i print t

(* Position results. *)
(* ************************************************************************ *)

(* What might wait at the end of a path. *)
type 'a res =
  | Var
  | Top of 'a Expr.function_descr Expr.id
  | Possible
  | Impossible

let print_res p fmt = function
  | Var -> Format.fprintf fmt "var"
  | Top f -> Format.fprintf fmt "top:%a" p f
  | Possible -> Format.fprintf fmt "possible"
  | Impossible -> Format.fprintf fmt "impossible"

(* Positions for Types *)
(* ************************************************************************ *)

module Ty = struct

  let rec apply p t = match p, t with
    | Here, { Expr.ty = Expr.TyVar _ }
    | Here, { Expr.ty = Expr.TyMeta _ } -> Var, Some t
    | Here, { Expr.ty = Expr.TyApp (f, _) } -> Top f, Some t
    | Arg _, { Expr.ty = Expr.TyVar _ }
    | Arg _, { Expr.ty = Expr.TyMeta _ } -> Possible, None
    | Arg (k, p'), { Expr.ty = Expr.TyApp(_, l) } ->
      begin match CCList.get_at_idx k l with
        | None -> Impossible, None
        | Some ty -> apply p' ty
      end

  let rec substitute p ~by:u t =
    match p, t with
    | Here, _ -> Some u
    | Arg (k, p'), { Expr.ty = Expr.TyApp(f, l) } ->
      CCOpt.map (Expr.Ty.apply ~status:t.Expr.ty_status f) @@ CCOpt.sequence_l
        (List.mapi (fun i v -> if i = k then substitute p' ~by:u v else Some v) l)
    | _ -> None

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.ty = Expr.TyApp (_, l) } ->
      CCList.foldi (fun acc i t ->
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

module Term = struct

  let rec apply p t = match p, t with
    | Here, { Expr.term = Expr.Var _ }
    | Here, { Expr.term = Expr.Meta _ } -> Var, Some t
    | Here, { Expr.term = Expr.App (f, _, _) } -> Top f, Some t
    | Arg _, { Expr.term = Expr.Var _ }
    | Arg _, { Expr.term = Expr.Meta _ } -> Possible, None
    | Arg (k, p'), { Expr.term = Expr.App(_, _, l) } ->
      begin match CCList.get_at_idx k l with
        | None -> Impossible, None
        | Some term -> apply p' term
      end

  let rec substitute p ~by:u t =
    match p, t with
    | Here, _ -> Some u
    | Arg (k, p'), { Expr.term = Expr.App(f, tys, l) } ->
      CCOpt.map (Expr.Term.apply ~status:t.Expr.t_status f tys) @@ CCOpt.sequence_l
        (List.mapi (fun i v -> if i = k then substitute p' ~by:u v else Some v) l)
    | _ -> None

  let rec fold_aux f acc cur_pos t =
    let acc' = f acc (cur_pos Here) t in
    match t with
    | { Expr.term = Expr.App (_, _, l) } ->
      CCList.foldi (fun acc i t ->
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
