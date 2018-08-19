(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)
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

let arg i t =
  if i >= 0 then Arg (i, t)
  else invalid_arg "Position.arg"

let rec concat t t' =
  match t with
  | Here -> t'
  | Arg(i, t'') -> Arg(i, concat t'' t')

let rec path = function
  | [] -> root
  | k :: r -> arg k (path r)

let follow t i = concat t (path [i])

(* Comparison, equality, printing. *)
let equal = (=)
let compare = Pervasives.compare

let rec print fmt = function
  | Here -> Format.fprintf fmt "."
  | Arg (i, t) -> Format.fprintf fmt "%d-%a" i print t

(* Position results. *)
(* ************************************************************************ *)

(* What might wait at the end of a path. *)
type ('a, 'b) res =
  | Var
  | Top of ('a, 'b) Expr.function_descr Expr.id
  | Possible
  | Impossible

let print_res p fmt = function
  | Var -> Format.fprintf fmt "var"
  | Top f -> Format.fprintf fmt "top:%a" p f
  | Possible -> Format.fprintf fmt "possible"
  | Impossible -> Format.fprintf fmt "impossible"

(* Positions for Proof terms *)
(* ************************************************************************ *)

module Proof = struct

  let rec apply p t =
    match p, t with
    | Here, _ -> Some t
    | Arg (0, p'), { Term.term = Term.App (t', _) }
    | Arg (1, p'), { Term.term = Term.App (_, t') }
    | Arg (0, p'), { Term.term = Term.Let (_, t', _) }
    | Arg (1, p'), { Term.term = Term.Let (_, _, t') }
    | Arg (0, p'), { Term.term = Term.Binder (_, _, t') }
      -> apply p' t'
    | Arg _, _ -> None

  let rec substitute p ~by:u t =
    match p, t with
    | Here, _ -> Some u
    | Arg (0, p'), { Term.term = Term.App (f, arg) } ->
      CCOpt.map (fun x -> Term.app x arg) (substitute p' ~by:u f)
    | Arg (1, p'), { Term.term = Term.App (f, arg) } ->
      CCOpt.map (fun x -> Term.app f x) (substitute p' ~by:u arg)
    | Arg (0, p'), { Term.term = Term.Let (v, e, body) } ->
      CCOpt.map (fun x -> Term.letin v x body) (substitute p' ~by:u e)
    | Arg (1, p'), { Term.term = Term.Let (v, e, body) } ->
      CCOpt.map (fun x -> Term.letin v e x) (substitute p' ~by:u body)
    | Arg (0, p'), { Term.term = Term.Binder (b, v, body) } ->
      CCOpt.map (fun x -> Term.bind b v x) (substitute p' ~by:u body)
    | Arg _, _ -> None

  let rec find_aux cur_pos u t =
    if Term.equal t u then Some (cur_pos Here)
    else begin match t with
      | { Term.term = Term.Type }
      | { Term.term = Term.Id _ } -> None
      | { Term.term = Term.App (f, arg) } ->
        CCOpt.or_lazy
          (find_aux (fun p -> cur_pos (Arg (0, p))) u f)
          ~else_:(fun () -> find_aux (fun p -> cur_pos (Arg (1, p))) u arg)
      | { Term.term = Term.Let (_, e, body) } ->
        CCOpt.or_lazy
          (find_aux (fun p -> cur_pos (Arg (0, p))) u e)
          ~else_:(fun () -> find_aux (fun p -> cur_pos (Arg (1, p))) u body)
      | { Term.term = Term.Binder (_, _, body) } ->
        find_aux (fun p -> cur_pos (Arg (0, p))) u body
    end

  let find = find_aux (fun x -> x)

end

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

