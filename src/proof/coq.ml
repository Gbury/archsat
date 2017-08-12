
module D = Dispatcher

let section = Section.make "coq"

(* Printing wrappers *)
(* ************************************************************************ *)

module Print = struct

  let pretty = Tag.create ()

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

  let rec formula_aux fmt f =
    let aux fmt f = match f.formula with
      | True | False -> formula_aux fmt f
      | _ -> Format.fprintf fmt "(@ %a@ )" formula_aux f
    in
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
    | Not f -> Format.fprintf fmt "@[<hov 2>~ %a@]" aux f

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

    | Imply (p, q) -> Format.fprintf fmt "@[<hov>%a@ =>@ %a@]" aux p aux q
    | Equiv (p, q) -> Format.fprintf fmt "@[<hov>%a@ <=>@ %a@]" aux p aux q

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
    | F f -> formula_aux fmt f
    | L l -> Format.fprintf fmt "(%a)" CCFormat.(list ~sep (tree ~sep)) l

  let formula = formula_aux

end

(* Printing mSAT proofs *)
(* ************************************************************************ *)

type _ Dispatcher.msg +=
  | Prove : Format.formatter * D.lemma_info -> unit Dispatcher.msg

module Lemma = struct

    (** Print mSAT atoms *)
    let print_atom fmt a =
      Print.formula fmt Dispatcher.SolverTypes.(a.lit)

    (** Prove assumptions.
        These raise en Error, because assumptions should only
        be used temporarily (to help with proof search). *)
    let prove_assumption fmt name clause = assert false

    (** Prove hypotheses. All hypothses (including negated goals)
        should already be available under their official names
        (i.e. full name of Dolmen id associated with the clause),
        so it should really just be a matter of introducing the right
        name for it. *)
    let prove_hyp fmt name clause =
      match Solver.hyp_id clause with
      | None -> assert false (* All hyps should must have been given an id. *)
      | Some id ->
        Format.fprintf fmt "(* Renaming hypothesis *)@\n";
        Format.fprintf fmt "pose proof %a as %s.@\n" Print.dolmen id name

    (** Prove lemmas.
        To ensure lemmas are proved in an empty and clean environment,
        We first prove them in a coq 'Lemma' (outside the main proof,
        since nested proofs are deprecated in Coq). *)

    (** Internal lemma name *)
    let lemma_name lemma =
      Format.sprintf "lemma_%d" lemma.Dispatcher.id

    let extract_lemma clause =
      match clause.Dispatcher.SolverTypes.cpremise with
      | Dispatcher.SolverTypes.Lemma lemma -> Some lemma
      | _ -> None

    (** First, a wrapper around the dispatcher's message system *)
    let print_lemma_proof fmt lemma =
      match Dispatcher.ask lemma.Dispatcher.plugin_name
              (Prove (fmt, lemma.Dispatcher.proof_info)) with
      | Some () -> ()
      | None ->
        Util.warn ~section "Got no coq proof from plugin %s for proof %s"
          lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
        Format.fprintf fmt
          "(* Got no proof from plugin, try and complete the proof by hand ? *)"

    (* Prove a lemma (outside of the main proof environment) *)
    let print_lemma fmt clause lemma =
      Format.fprintf fmt "@\n(* Proving lemma %s/%s *)@\n"
        lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
      Format.fprintf fmt "@[<hov 2>Lemma %s: %a.@]@\n@[<hv 2>Proof.@ %a@ Qed.@]@\n"
        (lemma_name lemma)
        CCFormat.(array ~sep:(return {|@ \/@ |}) print_atom)
        clause.Dispatcher.SolverTypes.atoms
        print_lemma_proof lemma

    let print_all fmt l =
      let aux c = CCOpt.iter (print_lemma fmt c) (extract_lemma c) in
      List.iter aux l

    let prove_lemma fmt name clause =
      let lemma = CCOpt.get_exn (extract_lemma clause) in
      Format.fprintf fmt "(* Import lemma %s as %s *)@\n" (lemma_name lemma) name;
      Format.fprintf fmt "pose proof %s as %s.@\n" (lemma_name lemma) name

  end

module M = Msat.Coq.Make(Solver.Proof)(Lemma)

(* Printing contexts *)
(* ************************************************************************ *)

let declare_ty fmt f =
  Format.fprintf fmt "Parameter %a.@\n" Print.const_ttype f

let declare_term fmt f =
  Format.fprintf fmt "Parameter %a.@\n" Print.const_ty f

let add_hyp fmt (id, f) =
  Format.fprintf fmt "Axiom %a : %a.@\n" Print.dolmen id Print.formula f

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
  | [x; y] ->
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, %a). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x Print.dolmen y i
  | x :: r ->
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, G%d). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x (i + 1) i;
    intro_aux fmt (i + 1) r

let pp_intro fmt l =
  match l with
  | [] -> () (* goal is already 'False', nothing to do *)
  | _ ->
    Format.fprintf fmt "(* Introduce the goal(s) into the hyps *)";
    Format.fprintf fmt "apply Coq.Logic.Classical_Prop.NNPP. ";
    begin match l with
      | [] -> assert false
      | [id] ->
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
  let () = Lemma.print_all fmt l in
  Format.fprintf fmt "@\nTheorem goal : @[<hov>%a@].@\n" pp_goals goals;
  Format.fprintf fmt "@[<hov 2>Proof.@\n%a@\n%a@]@\nQed.@." pp_intro names M.print proof


