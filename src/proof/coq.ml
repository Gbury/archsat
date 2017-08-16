
let section = Section.make "coq"

module M = Map.Make(Expr.Formula)

let formula a = a.Dispatcher.SolverTypes.lit

(* Printing wrappers *)
(* ************************************************************************ *)

module Print = struct

  let pretty = Tag.create ()

  let () =
    Expr.Id.tag Expr.Id.prop pretty (Expr.Print.Prefix "Prop")

  let () =
    Expr.Id.tag Expr.Id.base pretty (Expr.Print.Prefix "Set")

  let t =
    let name (Escape.Any.Id id) =
      match Expr.Id.get_tag id pretty with
      | None -> id.Expr.id_name
      | Some Expr.Print.(Infix s | Prefix s) -> s
    in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          let g = Uucp.Gc.general_category c in
          begin match g with
            | `Lu | `Ll | `Lt | `Lm | `Lo | `Sm -> [ c ]
            | `Nd when i > 1 -> [ c ]
            | _ -> [ Uchar.of_char '_' ]
          end) in
    Escape.mk ~lang:"coq" ~name ~escape ~rename

  let dolmen fmt id =
    Escape.print_string t fmt (Dolmen.Id.full_name id)

  open Expr

  let id fmt v =
    Escape.print t fmt v

  let meta fmt m =
    (* metas should be replaced by someting else,
       for instance an arbitrary ground term of its type *)
    assert false

  let ttype fmt = function Type -> Format.fprintf fmt "Type"

  let rec ty fmt t = match t.ty with
    | TyVar v -> id fmt v
    | TyMeta m -> meta fmt m
    | TyApp (f, []) -> id fmt f
    | TyApp (f, l) ->
      begin match Tag.get f.id_tags pretty with
        | None | Some Print.Prefix _ ->
          Format.fprintf fmt "@[<hov 1>(%a@ %a)@]"
            id f CCFormat.(list ~sep:(return "@ ") ty) l
        | Some Print.Infix _ ->
          let sep fmt () = Format.fprintf fmt "@ %a@ " id f in
          Format.fprintf fmt "@[<hov 1>(%a)@]" (CCFormat.list ~sep ty) l
      end

  let params pp fmt = function
    | [] -> ()
    | l ->
      let aux fmt v =
        Format.fprintf fmt "@[<h>(%a :@ %a)@]@ "
          id v pp v.id_type
      in
      Format.fprintf fmt "forall @[<hov>%a@],@ "
        CCFormat.(list ~sep:(return "@ ") aux) l

  let signature print fmt f =
    match f.fun_args with
    | [] ->
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params ttype) f.fun_vars print f.fun_ret
    | l ->
      Format.fprintf fmt "@[<hov 2>%a%a ->@ %a@]"
        (params ttype) f.fun_vars
        CCFormat.(list ~sep:(return " ->@ ") print) l print f.fun_ret

  let fun_ty = signature ty
  let fun_ttype = signature ttype

  let id_type print fmt v =
    Format.fprintf fmt "@[<hov 2>%a :@ %a@]" id v print v.id_type

  let id_ty = id_type ty
  let id_ttype = id_type ttype
  let const_ty = id_type fun_ty
  let const_ttype = id_type fun_ttype

  let rec term fmt t = match t.term with
    | Var v -> id fmt v
    | Meta m -> meta fmt m
    | App (f, [], []) -> id fmt f
    | App (f, tys, args) ->
      begin match Tag.get f.id_tags pretty with
        | None | Some Print.Prefix _ ->
          begin match tys with
            | [] ->
              Format.fprintf fmt "(@[<hov>%a@ %a@])"
                id f CCFormat.(list ~sep:(return "@ ") term) args
            | _ ->
              Format.fprintf fmt "(@[<hov>%a@ %a@ %a@])" id f
                CCFormat.(list ~sep:(return "@ ") ty) tys
                CCFormat.(list ~sep:(return "@ ") term) args
          end
        | Some Print.Infix _ ->
          assert (tys = []);
          let sep fmt () = Format.fprintf fmt "@ %a@ " id f in
          Format.fprintf fmt "(%a)" CCFormat.(list ~sep term) args
      end

  let rec formula fmt f =
    match f.formula with
    | True | False | Not _
    | Pred ({ term = App (_, [], [])})
    | And _ | Or _ -> formula_aux fmt f
    | _ -> Format.fprintf fmt "( %a )" formula_aux f

  and formula_aux fmt f =
    match f.formula with
    | Pred t -> Format.fprintf fmt "%a" term t
    | Equal (a, b) ->
      let x, y =
        match Formula.get_tag f t_order with
        | None -> assert false
        | Some Same -> a, b
        | Some Inverse -> b, a
      in
      Format.fprintf fmt "@[<hov>%a@ =@ %a@]" term x term y

    | True  -> Format.fprintf fmt "True"
    | False -> Format.fprintf fmt "False"
    | Not f -> Format.fprintf fmt "@[<hov 2>~ %a@]" formula f

    | And l ->
      begin match Formula.get_tag f f_order with
        | None -> assert false
        | Some order ->
          let sep = CCFormat.return {| /\@ |} in
          Format.fprintf fmt "@[<hov>%a@]" (tree ~sep) order
      end
    | Or l  ->
      begin match Formula.get_tag f f_order with
        | None -> assert false
        | Some order ->
          let sep = CCFormat.return {| \/@ |} in
          Format.fprintf fmt "@[<hov>%a@]" (tree ~sep) order
      end

    | Imply (p, q) -> Format.fprintf fmt "@[<hov>%a@ ->@ %a@]" formula p formula q
    | Equiv (p, q) -> Format.fprintf fmt "@[<hov>%a@ <->@ %a@]" formula p formula q

    | All (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>forall @[<hov>%a@],@ %a@]"
        (params ty) l formula_aux f
    | AllTy (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>forall @[<hov>%a@],@ %a@]"
        (params ttype) l formula_aux f
    | Ex (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>exists @[<hov>%a@],@ %a@]"
        (params ty) l formula_aux f
    | ExTy (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>exists @[<hov>%a@],@ %a@]"
        (params ttype) l formula_aux f

  and tree ~sep fmt = function
    | F f -> formula fmt f
    | L l -> Format.fprintf fmt "(%a)" CCFormat.(list ~sep (tree ~sep)) l

  let atom fmt a =
    formula fmt Dispatcher.SolverTypes.(a.lit)

  let rec pattern ~start ~stop ~sep pp fmt = function
    | L [] -> assert false
    | F f -> pp fmt f
    | L [x] ->
      pattern ~start ~stop ~sep pp fmt x
    | L (x :: r) ->
      Format.fprintf fmt "%a%a%a%a%a"
        start ()
        (pattern ~start ~stop ~sep pp) x
        sep ()
        (pattern ~start ~stop ~sep pp) (Expr.L r)
        stop ()

  let pattern_or =
    let open CCFormat in
    pattern ~start:(return "[") ~stop:(return "]") ~sep:(return " | ")

  let pattern_and =
    let open CCFormat in
    pattern ~start:(return "[") ~stop:(return "]") ~sep:(return " ")

  let pattern_intro_and =
    let open CCFormat in
    pattern ~start:(return "(conj@ ") ~stop:(return ")") ~sep:(return "@ ")

  let rec path_aux fmt (i, n) =
    if i = 1 then
      Format.fprintf fmt "left"
    else begin
      Format.fprintf fmt "right";
      if n = 2 then assert (i = 2)
      else Format.fprintf fmt ";@ %a" path_aux (i - 1, n - 1)
    end

  let path fmt (i, n) =
    if i <= 0 || i > n then raise (Invalid_argument "Coq.Print.path")
    else Format.fprintf fmt "@[<hov>%a@]" path_aux (i, n)

  let rec exists_in_order f = function
    | F g -> Expr.Formula.equal f g
    | L l -> List.exists (exists_in_order f) l

  let path_to fmt (goal, order) =
    let rec aux acc = function
      | F g ->
        assert (Expr.Formula.equal goal g);
        List.rev acc
      | L l ->
        begin match CCList.find_idx (exists_in_order goal) l with
        | None -> assert false
        | Some (i, o) ->
          let n = List.length l in
          aux ((i + 1, n) :: acc) o
        end
    in
    let l = aux [] order in
    Format.fprintf fmt "@[<hov>%a@]" CCFormat.(list ~sep:(return ";@ ") path_aux) l

end

(* Printing contexts *)
(* ************************************************************************ *)

(** Keep in mind the relation Dolmen id -> clause *)
module H = Hashtbl.Make(Dolmen.Id)

let hyp_table = H.create 1013

let declare_ty fmt f =
  Format.fprintf fmt "Parameter %a.@." Print.const_ttype f

let declare_term fmt f =
  Format.fprintf fmt "Parameter %a.@." Print.const_ty f

let add_hyp fmt (id, l) =
  H.add hyp_table id l;
  Format.fprintf fmt "Axiom %a : @[<hov>%a@].@." Print.dolmen id
    CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula) l

(* Proving plugin's lemmas *)
(* ************************************************************************ *)

(** Types for different proof styles *)
type raw_proof = Format.formatter -> unit -> unit

type ordered_proof = {
  order : Expr.formula list;
  proof : raw_proof;
}

type impl_proof = {
  prefix  : string;
  left    : Expr.formula list;
  right   : Expr.formula list;
  proof   : Format.formatter -> string M.t -> unit;
}

type proof_style =
  | Raw of raw_proof
  | Ordered of ordered_proof
  | Implication of impl_proof

type _ Dispatcher.msg +=
  | Prove : Dispatcher.lemma_info -> proof_style Dispatcher.msg


(** Internal lemma name *)
let lemma_name lemma =
  Format.sprintf "lemma_%d" lemma.Dispatcher.id

let extract_lemma clause =
  match clause.Dispatcher.SolverTypes.cpremise with
  | Dispatcher.SolverTypes.Lemma lemma -> Some lemma
  | _ -> None


(** Small wrapper around the dispatcher's message system *)
let lemma_proof lemma =
  match Dispatcher.ask lemma.Dispatcher.plugin_name
          (Prove (lemma.Dispatcher.proof_info)) with
  | Some p -> p
  | None ->
    Util.warn ~section "Got no coq proof from plugin %s for proof %s"
      lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
    Raw (fun fmt () ->
        Format.fprintf fmt
          "(* Got no proof from plugin, try and complete the proof by hand ? *)")

let proof_order clause = function
  | Raw proof ->
    List.map formula @@ Array.to_list clause.Dispatcher.SolverTypes.atoms
  | Ordered { order ; proof } ->
    (** Check that the given ordered clause if included in the one
        we have to prove. *)
    assert (List.for_all (fun f -> Array.exists (fun a ->
        Expr.Formula.equal f (formula a)
      ) clause.Dispatcher.SolverTypes.atoms) order);
    order
  | Implication { prefix; left; right; proof; } ->
    (** Check that the given ordered clause if included in the one
        we have to prove. *)
    assert (List.for_all (fun f -> Array.exists (fun a ->
        Expr.Formula.equal (Expr.Formula.neg f) (formula a)
      ) clause.Dispatcher.SolverTypes.atoms) left);
    assert (List.for_all (fun f -> Array.exists (fun a ->
        Expr.Formula.equal f (formula a)
      ) clause.Dispatcher.SolverTypes.atoms) right);
    List.map Expr.Formula.neg left @ right

let proof_printer clause = function
  | Raw proof | Ordered { proof; _ } -> proof
  | Implication { prefix; left; proof; } ->
    fun fmt () ->
      let _, m = List.fold_left (fun (i, acc) f ->
          let name = Format.sprintf "%s%d" prefix i in
          (i + 1, M.add f name acc)) (0, M.empty) left
      in
      let () = List.iter (fun f ->
          Format.fprintf fmt
            "apply Coq.Logic.Classical_Prop.imply_to_or; intro %s.@ "
            (M.find f m)) left
      in
      proof fmt m

let pp_break fmt (i, j) = Format.pp_print_break fmt i j

(* Prove a lemma (outside of the main proof environment) *)
let print_lemma fmt clause lemma =
  let proof = lemma_proof lemma in
  Format.fprintf fmt "@\n(* Proving lemma %s/%s *)@\n"
    lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
  Format.fprintf fmt "@[<hov 2>Lemma %s: %a.@]@\n@[<hv 2>Proof.@ %a%aQed.@]@\n"
    (lemma_name lemma)
    CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula)
    (proof_order clause proof)
    (proof_printer clause proof) ()
    pp_break (1,-2)

let print_lemmas fmt l =
  let aux c = CCOpt.iter (print_lemma fmt c) (extract_lemma c) in
  List.iter aux l

(* Printing mSAT proofs *)
(* ************************************************************************ *)

module Lemma = struct

  (** Print mSAT atoms *)
  let print_atom = Print.atom

  (** Prove assumptions.
      These raise en Error, because assumptions should only
      be used temporarily (to help with proof search).
      TODO:use a proper exception instead of assert false *)
  let prove_assumption fmt name clause = assert false

  (** clausify or-separated clauses into mSAT encoding of clauses *)
  let clausify fmt (orig, l, dest, a) =
    (** assert goal clause *)
    let pp_atom fmt atom =
      let pos = Dispatcher.SolverTypes.(atom.var.pa) in
      if atom == pos then
        Format.fprintf fmt "~ %a" Print.atom atom
      else
        Format.fprintf fmt "~ ~ %a" Print.atom pos
    in
    Format.fprintf fmt "assert (%s: @[<hov>%a@ ->@ False@]).@ " dest
      CCFormat.(array ~sep:(return " ->@ ") pp_atom) a;
    let _, m = Array.fold_left (fun (i, acc) atom ->
        let name = Format.sprintf "Ax%d" i in
        (i + 1, M.add (formula atom) (name, formula atom) acc)) (0, M.empty) a in
    let aux fmt atom = Format.fprintf fmt "%s" (fst @@ M.find (formula atom) m) in
    Format.fprintf fmt "intros %a.@ " CCFormat.(array ~sep:(return " ") aux) a;
    (** wrapper around equalities to reorder them *)
    let pp_exact fmt (f, s) =
      let name, f' = M.find f m in
      match f with
      | { Expr.formula = Expr.Equal _ } ->
        let t = CCOpt.get_exn (Expr.Formula.get_tag f Expr.t_order) in
        let t' = CCOpt.get_exn (Expr.Formula.get_tag f' Expr.t_order) in
        if t = t'
        then Format.fprintf fmt "%s %s" name s
        else Format.fprintf fmt "%s (eq_sym %s)" name s
      | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equal _ } as r) } ->
        begin match f' with
          | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equal _ } as r') } ->
            let t = CCOpt.get_exn (Expr.Formula.get_tag r Expr.t_order) in
            let t' = CCOpt.get_exn (Expr.Formula.get_tag r' Expr.t_order) in
            if t = t'
            then Format.fprintf fmt "%s %s" name s
            else Format.fprintf fmt "%s (not_eq_sym %s)" name s
          | _ -> assert false
        end
      | _ -> Format.fprintf fmt "%s %s" name s
    in
    (** destruct already proved hyp *)
    match l with
    | [] -> assert false
    | [p] ->
      Format.fprintf fmt "exact (%a)." pp_exact (p, orig)
    | _ ->
      let order = Expr.L (List.map (fun f -> Expr.F f) l) in
      Format.fprintf fmt "@[<hov 2>destruct %s as %a.@ %a@]" orig
        (Print.pattern_or (fun fmt _ -> Format.fprintf fmt "T")) order
      CCFormat.(list ~sep:(return "@ ") (fun fmt f ->
          if Expr.Formula.(equal f_false) f then
            Format.fprintf fmt "exact T."
          else
            Format.fprintf fmt "exact (%a)." pp_exact (f, "T")
        )) l

  (** Prove hypotheses. All hypothses (including negated goals)
      should already be available under their official names
      (i.e. full name of Dolmen id associated with the clause),
      so it should really just be a matter of introducing the right
      name for it. *)
  let prove_hyp fmt name clause =
    match Solver.hyp_id clause with
    | None -> assert false (* All hyps should must have been given an id. *)
    | Some id ->
      Format.fprintf fmt "(* Introducing hypothesis %a as %s *)@\n%a@\n"
        Print.dolmen id name clausify
        ((Format.asprintf "%a" Print.dolmen id), (H.find hyp_table id),
         name, clause.Dispatcher.SolverTypes.atoms)

  (** Prove lemmas.
      To ensure lemmas are proved in an empty and clean environment,
      We first prove them in a coq 'Lemma' (outside the main proof,
      since nested proofs are deprecated in Coq). *)
  let prove_lemma fmt name clause =
    let lemma = CCOpt.get_exn (extract_lemma clause) in
    Format.fprintf fmt "(* Import lemma %s as %s *)@\n%a@\n"
      (lemma_name lemma) name
      clausify
      ((lemma_name lemma), (proof_order clause (lemma_proof lemma)),
       name, clause.Dispatcher.SolverTypes.atoms)

end

module P = Msat.Coq.Make(Solver.Proof)(Lemma)

(* Printing proofs *)
(* ************************************************************************ *)

(** Introduce the goals as hypotheses, using diabolical classical logic !!
    Separated into two functions. Depends on the number of goals:
    - 0 goals : nothing to do, ^^
    - 1 goal  : NNPP, and intro
    - n goals : NNPP, and deMorgan to decompose the '~ (\/ a_i)'
                into hypotheses '~ a_i' *)
let rec intro_aux fmt i = function
  | [] | [_] -> assert false
  | [x, gx; y, gy] ->
    H.add hyp_table x [gx];
    H.add hyp_table y [gy];
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, %a). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x Print.dolmen y i
  | (x, gx) :: r ->
    H.add hyp_table x [gx];
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, G%d). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x (i + 1) i;
    intro_aux fmt (i + 1) r

let pp_intro fmt l =
  match l with
  | [] -> () (* goal is already 'False', nothing to do *)
  | _ ->
    Format.fprintf fmt "(* Introduce the goal(s) into the hyps *)@\n";
    Format.fprintf fmt "apply Coq.Logic.Classical_Prop.NNPP. ";
    begin match l with
      | [] -> assert false
      | [id, g] ->
        H.add hyp_table id [g];
        Format.fprintf fmt "intro %a.@\n" Print.dolmen id
      | _ ->
        Format.fprintf fmt "intro G0.@\n";
        intro_aux fmt 0 l
    end

(** Record named goals to ouput a proper theorem later *)
let _goals = ref []

let add_goal _ (id, g) =
  _goals := (id, g) :: !_goals

let get_goals () =
  let l = !_goals in
  _goals := [];
  l

(** Print both the goals (as theorem), and its proof. *)
let print_proof fmt proof =
  Format.pp_set_margin fmt 100;
  let names, goals = List.split (get_goals ()) in
  let pp_goals fmt = function
    | [] -> Format.fprintf fmt "False"
    | l -> CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula) fmt l
  in
  Format.fprintf fmt "@\n(* Coq proof generated by Archsat *)@\n@\n";
  Format.fprintf fmt "Require Import Coq.Logic.Classical_Prop.@\n";
  let l = Solver.Proof.unsat_core proof in
  let () = print_lemmas fmt l in
  Format.fprintf fmt "@\nTheorem goal : @[<hov>%a@].@\n" pp_goals goals;
  Format.fprintf fmt "@[<hov 2>Proof.@\n%a@\n%a@]@\nQed.@."
    pp_intro (List.combine names (List.map Expr.Formula.neg goals))
    P.print proof


