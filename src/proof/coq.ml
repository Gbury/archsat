
let section = Section.make "coq"

let formula a = a.Dispatcher.SolverTypes.lit

(* Type definitions *)
(* ************************************************************************ *)

type prelude =
  | Require : string -> prelude
  | Notation : 'a Expr.id * (Format.formatter -> 'a Expr.id -> unit) -> prelude

type raw_proof = {
  prelude : prelude list;
  proof : Format.formatter -> unit -> unit;
}

type ordered_proof = {
  prelude : prelude list;
  order : Expr.formula list;
  proof : Format.formatter -> unit -> unit;
}

type impl_proof = {
  prelude : prelude list;
  prefix  : string;
  left    : Expr.formula list;
  right   : Expr.formula list;
  proof   : Format.formatter -> Proof.Ctx.t -> unit;
}

type proof_style =
  | Raw of raw_proof
  | Ordered of ordered_proof
  | Implication of impl_proof

type _ Dispatcher.msg +=
  | Prove : Dispatcher.lemma_info -> proof_style Dispatcher.msg

(* Printing wrappers *)
(* ************************************************************************ *)

module Print = struct

  (** Traps are there to enforce translation of certain
      types of terms into another type/term. *)
  module Hty = Hashtbl.Make(Expr.Ty)
  module Hterm = Hashtbl.Make(Expr.Term)

  let ty_traps = Hty.create 13
  let term_traps = Hterm.create 13

  let trap_ty = Hty.add ty_traps
  let trap_term = Hterm.add term_traps

  open Expr

  let pretty = Tag.create ()

  let () =
    Expr.Id.tag Expr.Id.prop pretty (Print.Prefix "Prop")

  let () =
    Expr.Id.tag Expr.Id.base pretty (Print.Prefix "Set")

  let t =
    let name = function
      | Escape.Any.Dolmen id -> Dolmen.Id.full_name id
      | Escape.Any.Id id ->
        begin match Expr.Id.get_tag id pretty with
        | None -> id.Expr.id_name
        | Some (Print.Infix s | Print.Prefix s) -> s
        end
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

  let dolmen fmt id = Escape.dolmen t fmt id

  let id fmt v = Escape.id t fmt v

  let ttype fmt = function Expr.Type -> Format.fprintf fmt "Type"

  let rec ty fmt t =
    match Hty.find ty_traps t with
    | t' -> ty fmt t'
    | exception Not_found ->
      begin match t.ty with
        | TyVar v -> id fmt v
        | TyMeta m -> ty fmt Synth.ty
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
      end

  let params pre pp fmt = function
    | [] -> ()
    | l ->
      let aux fmt v =
        Format.fprintf fmt "@[<h>(%a :@ %a)@]@ "
          id v pp v.id_type
      in
      Format.fprintf fmt "%s @[<hov>%a@],@ "
        pre CCFormat.(list ~sep:(return "@ ") aux) l

  let signature print fmt f =
    match f.fun_args with
    | [] ->
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params "forall" ttype) f.fun_vars print f.fun_ret
    | l ->
      Format.fprintf fmt "@[<hov 2>%a%a ->@ %a@]"
        (params "forall" ttype) f.fun_vars
        CCFormat.(list ~sep:(return " ->@ ") print) l print f.fun_ret

  let fun_ty = signature ty
  let fun_ttype = signature ttype

  let id_type print fmt v =
    Format.fprintf fmt "@[<hov 2>%a :@ %a@]" id v print v.id_type

  let id_ty = id_type ty
  let id_ttype = id_type ttype
  let const_ty = id_type fun_ty
  let const_ttype = id_type fun_ttype

  let rec term fmt t =
    match Hterm.find term_traps t with
    | t' -> term fmt t'
    | exception Not_found ->
      begin match t.term with
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
      end

  and meta fmt m =
    match Synth.term m.meta_id.id_type with
    | None -> assert false
    | Some t -> term fmt t

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
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params "forall" ty) l formula_aux f
    | AllTy (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params "forall" ttype) l formula_aux f
    | Ex (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params "exists" ty) l formula_aux f
    | ExTy (l, _, f) ->
      Format.fprintf fmt "@[<hov 2>%a%a@]"
        (params "exists" ttype) l formula_aux f

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

  let pattern_or pp fmt =
    let open CCFormat in
    pattern ~start:(return "[") ~stop:(return "]") ~sep:(return " | ") pp fmt

  let pattern_and pp fmt =
    let open CCFormat in
    pattern ~start:(return "[") ~stop:(return "]") ~sep:(return " ") pp fmt

  let pattern_ex pp fmt =
    let open CCFormat in
    pattern ~start:(return "[") ~stop:(return "]") ~sep:(return " ") pp fmt

  let pattern_intro_and pp fmt =
    let open CCFormat in
    pattern ~start:(return "(conj@ ") ~stop:(return ")") ~sep:(return "@ ") pp fmt

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

let declare_ty fmt f =
  Format.fprintf fmt "Parameter %a.@." Print.const_ttype f

let declare_term fmt f =
  Format.fprintf fmt "Parameter %a.@." Print.const_ty f

let print_hyp fmt (id, l) =
  Format.fprintf fmt "Axiom %a : @[<hov>%a@].@." Print.dolmen id
    CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula) l

(* Coq proof helpers *)
(* ************************************************************************ *)

let exact fmt format =
  Format.fprintf fmt ("exact (" ^^ format ^^ ").")

let pose_proof ctx f fmt format =
  Format.kfprintf (fun fmt ->
      Format.fprintf fmt ") as %a." (Proof.Ctx.named ctx) f)
    fmt ("pose proof (" ^^ format)


let fun_binder fmt args =
  CCFormat.(list ~sep:(return "@ ") Print.id) fmt args

let app_t ctx fmt (f, l) =
  Format.fprintf fmt "%a @[<hov>%a@]"
    (Proof.Ctx.named ctx) f CCFormat.(list ~sep:(return "@ ") Print.term) l

let sequence ctx pp start fmt l =
  let rec aux ctx pp fmt curr = function
    | [] -> curr
    | x :: r ->
      let next = Proof.Ctx.new_name ctx in
      Format.fprintf fmt "pose proof (%a) as %s.@ " (pp curr) x next;
      aux ctx pp fmt next r
  in
  aux ctx pp fmt start l

(* Proving plugin's lemmas *)
(* ************************************************************************ *)

module Lemma = struct

  (** Internal lemma name *)
  let name lemma =
    Format.sprintf "lemma_%d" lemma.Dispatcher.id

  let extract clause =
    match clause.Dispatcher.SolverTypes.cpremise with
    | Dispatcher.SolverTypes.Lemma lemma -> Some lemma
    | _ -> None

  (** Small wrapper around the dispatcher's message system
      Also memoise proofs using a hashtbl. *)
  let _proofs = Hashtbl.create 4013

  let get_proof lemma =
    try Hashtbl.find _proofs lemma.Dispatcher.id
    with Not_found ->
      let res =
        match Dispatcher.ask lemma.Dispatcher.plugin_name
                (Prove (lemma.Dispatcher.proof_info)) with
        | Some p -> p
        | None ->
          Util.warn ~section "Got no coq proof from plugin %s for proof %s"
            lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
          Raw {
            prelude = [];
            proof = fun fmt () ->
              Format.fprintf fmt
                "(* Got no proof from plugin, try and complete the proof by hand ? *)"
          }
      in
      let () = Hashtbl.add _proofs lemma.Dispatcher.id res in
      res

  let proof_order clause = function
    | Raw proof ->
      List.map formula @@ Array.to_list clause.Dispatcher.SolverTypes.atoms
    | Ordered { order ; proof } ->
      (** Check that the given ordered clause if included in the one
          we have to prove. *)
      if not (List.for_all (fun f -> Array.exists (fun a ->
          Expr.Formula.equal f (formula a)
        ) clause.Dispatcher.SolverTypes.atoms) order) then
        raise (Dispatcher.Bad_assertion (
            Format.asprintf "Wrong clause for ordered lemma:@\n%a@\n%a"
              Dispatcher.SolverTypes.pp_clause clause
              CCFormat.(list ~sep:(return " //@ ") Print.formula) order))
      else
        order
    | Implication { prefix; left; right; proof; } ->
      (** Check that the given ordered clause if included in the one
          we have to prove. *)
      if not (List.for_all (fun f -> Array.exists (fun a ->
          Expr.Formula.equal (Expr.Formula.neg f) (formula a)
        ) clause.Dispatcher.SolverTypes.atoms) left) then
        raise (Dispatcher.Bad_assertion (
            Format.asprintf "Wrong hyp for implication lemma:@\n%a@\n%a"
              Dispatcher.SolverTypes.pp_clause clause
              CCFormat.(list ~sep:(return " //@ ") Print.formula) left))
      else if not (List.for_all (fun f -> Array.exists (fun a ->
          Expr.Formula.equal f (formula a)
        ) clause.Dispatcher.SolverTypes.atoms) right) then
        raise (Dispatcher.Bad_assertion (
            Format.asprintf "Wrong conclusion for implication lemma:@\n%a@\n%a"
              Dispatcher.SolverTypes.pp_clause clause
              CCFormat.(list ~sep:(return " //@ ") Print.formula) right))
      else
        List.map Expr.Formula.neg left @ right

  let proof_printer clause = function
    | Raw { proof; _ } | Ordered { proof; _ } -> proof
    | Implication { prefix; left; proof; } ->
      fun fmt () ->
        let ctx = Proof.Ctx.mk ~prefix () in
        let () = List.iter (fun f ->
            Format.fprintf fmt
              "apply Coq.Logic.Classical_Prop.imply_to_or; intro %a.@ "
              (Proof.Ctx.named ctx) f
          ) left
        in
        proof fmt ctx

  let pp_break fmt (i, j) = Format.pp_print_break fmt i j

  (* Prove a lemma (outside of the main proof environment) *)
  let print fmt clause lemma =
    Util.debug ~section "@[<hv>Proving theory lemma %s/%s:@ @[<hov>%a@]@]"
      lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name
      Dispatcher.SolverTypes.pp_clause clause;
    let proof = get_proof lemma in
    Format.fprintf fmt "@\n(* Proving lemma %s/%s *)@\n"
      lemma.Dispatcher.plugin_name lemma.Dispatcher.proof_name;
    Format.fprintf fmt "@[<hov 2>Lemma %s: %a.@]@\n@[<hv 2>Proof.@ %a%aQed.@]@\n"
      (name lemma)
      CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula)
      (proof_order clause proof)
      (proof_printer clause proof) ()
      pp_break (1,-2)

  let print_all fmt l =
    let aux c = CCOpt.iter (print fmt c) (extract c) in
    List.iter aux l

end

(* Printing mSAT proofs *)
(* ************************************************************************ *)

module P = Msat.Coq.Make(Solver.Proof)(struct

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
      Format.fprintf fmt "assert (%s: @[<hv>%a ->@ False@]).@ " dest
        CCFormat.(array ~sep:(return " ->@ ") pp_atom) a;
      let ctx = Proof.Ctx.mk ~prefix:"Ax" () in
      let aux fmt atom = Proof.Ctx.named ctx fmt (formula atom) in
      Format.fprintf fmt "intros %a.@ " CCFormat.(array ~sep:(return " ") aux) a;
      (** wrapper around equalities to reorder them *)
      let pp_exact fmt (f, s) =
        let f', name = Proof.Ctx.find ctx f in
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
          ((Format.asprintf "%a" Print.dolmen id), (Proof.find_hyp id),
           name, clause.Dispatcher.SolverTypes.atoms)

    (** Prove lemmas.
        To ensure lemmas are proved in an empty and clean environment,
        We first prove them in a coq 'Lemma' (outside the main proof,
        since nested proofs are deprecated in Coq). *)
    let prove_lemma fmt name clause =
      let lemma = CCOpt.get_exn (Lemma.extract clause) in
      Format.fprintf fmt "(* Import lemma %s as %s *)@\n%a@\n"
        (Lemma.name lemma) name
        clausify
        ((Lemma.name lemma), (Lemma.proof_order clause (Lemma.get_proof lemma)),
         name, clause.Dispatcher.SolverTypes.atoms)

  end)

(* Proof prelude *)
(* ************************************************************************ *)

module Prelude_t = struct

  (** Standard functions *)
  type t = prelude

  let _string s s' =
    CCOrd.((map String.length compare) s s'
           <?> (compare, s, s'))

  let _discr = function
    | Require _ -> 0
    | Notation _ -> 0

  let hash = function
    | Require s ->
      CCHash.(pair int string) (0, s)
    | Notation (id, s) ->
      CCHash.(pair int Expr.Id.hash) (1, id)

  let compare p p' =
    match p, p' with
    | Require s, Require s' -> _string s s'
    | Notation (id, s), Notation (id', s') ->
      (** Only one notation per id is authorized *)
      compare id.Expr.index id'.Expr.index
    | _ -> compare (_discr p) (_discr p')

  let equal p p' = compare p p' = 0

  let print fmt = function
    | Require s ->
      Format.fprintf fmt "Require Import %s.@ " s
    | Notation (id, f) ->
      Format.fprintf fmt "Notation %a := @[<hov 1>(%a)@].@ "
        Print.id id f id

end

module Prelude = struct

  include Prelude_t

  (** Set of preludes *)
  module S = Set.Make(Prelude_t)

  (** Dependencies between preludes *)
  module G = Graph.Imperative.Digraph.Concrete(Prelude_t)
  module T = Graph.Topological.Make_stable(G)
  module O = Graph.Oper.I(G)

  let g = G.create ()

  let mk ~deps t =
    let () = G.add_vertex g t in
    let () = S.iter (fun x -> G.add_edge g x t) deps in
    t

  let require ?(deps=S.empty) s = mk ~deps (Require s)

  let abbrev ?(deps=S.empty) id pp = mk ~deps (Notation (id, pp))

  (** Standard values *)
  let epsilon = require "Coq.Logic.Epsilon"
  let classical = require "Coq.Logic.Classical"

  let topo iter l =
    let _ = O.add_transitive_closure ~reflexive:true g in
    T.iter (fun v -> if S.exists (G.mem_edge g v) l then iter v) g

end

module Preludes = struct

  (** Efficient storing of global prelude *)

  let add t p = Prelude.S.add p t

  let empty ~goal =
    let t = Prelude.S.empty in
    if goal then add t Prelude.classical else t

  let get_prelude = function
    | Raw { prelude; _ }
    | Ordered { prelude; _ }
    | Implication { left = []; prelude; _ } -> prelude
    | Implication { prelude; _ } -> Prelude.classical :: prelude

  let gather t l =
    List.fold_left (fun acc lemma ->
        let p = Lemma.get_proof lemma in
        List.fold_left add acc (get_prelude p)
      ) t (CCList.filter_map Lemma.extract l)

  let print fmt l =
    Prelude.topo (Prelude.print fmt) l

end

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
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, %a). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x Print.dolmen y i
  | (x, gx) :: r ->
    Format.fprintf fmt "destruct (%s _ _ G%d) as (%a, G%d). clear G%d.@\n"
      "Coq.Logic.Classical_Prop.not_or_and" i Print.dolmen x (i + 1) i;
    intro_aux fmt (i + 1) r

let pp_intros fmt l =
  match l with
  | [] -> () (* goal is already 'False', nothing to do *)
  (** When a single goal is *not* is negation, it means that it is
      originally a negation, so we can directly introduce it. *)
  | [ id, { Expr.formula = (Expr.Not _ | Expr.True )} ] ->
    Format.fprintf fmt "(* Introduce the goal(s) into the hyps *)@\n";
    Format.fprintf fmt "apply Coq.Logic.Classical_Prop.NNPP. ";
    Format.fprintf fmt "intro %a.@\n" Print.dolmen id
  (** Interesting case (faster than match every other variant) *)
  | [ id, _ ] ->
    Format.fprintf fmt "(* Introduce the goal(s) into the hyps *)@\n";
    Format.fprintf fmt "intro %a.@\n" Print.dolmen id
  (** General case *)
  | _ ->
    Format.fprintf fmt "(* Introduce the goal(s) into the hyps *)@\n";
    Format.fprintf fmt "apply Coq.Logic.Classical_Prop.NNPP. ";
    begin match l with
      | [] -> assert false
      | [id, g] ->
        Format.fprintf fmt "intro %a.@\n" Print.dolmen id
      | _ ->
        Format.fprintf fmt "intro G0.@\n";
        intro_aux fmt 0 l
    end

let pp_goals fmt = function
  | [] -> Format.fprintf fmt "False"
  | l -> CCFormat.(list ~sep:(return {|@ \/@ |}) Print.formula) fmt l

(** Print both the goals (as theorem), and its proof. *)
let print_proof fmt proof =
  Format.pp_set_margin fmt 100;
  let names, goals = List.split (Proof.get_goals ()) in
  let l = Solver.Proof.unsat_core proof in
  let goal = match goals with [] -> false | _ -> true in
  let prelude = Preludes.(gather (empty ~goal) l) in
  Format.fprintf fmt "@\n(* Coq proof generated by Archsat *)@\n@\n";
  Format.fprintf fmt "@[<v>%a@]@\n%a" Preludes.print prelude Lemma.print_all l;
  Format.fprintf fmt "@\nTheorem goal : @[<hov>%a@].@\n" pp_goals goals;
  let l' = List.combine names (List.map Expr.Formula.neg goals) in
  Format.fprintf fmt
    "@[<hov 2>Proof.@\n%a@\n%a@]@\nQed.@."
    pp_intros l' P.print proof


