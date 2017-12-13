
let section = Section.make ~parent:Dispatcher.section "inst"

type lemma_info = Formula of Expr.formula * Mapping.t * Expr.formula

type Dispatcher.lemma_info += Inst of lemma_info

(* Metavariable positions *)
(* ************************************************************************ *)

module Hf = Hashtbl.Make(Expr.Formula)

type cluster =
  | Root of Expr.formula
  | Under of Expr.formula * cluster

let rec root = function
  | Root f -> f
  | Under (_, c) -> root c

let rec depth = function
  | Root _ -> 0
  | Under (_, c) -> 1 + depth c

let rec dive n = function
  | c when n <= 0 -> c
  | Root _ (* n > 0 *) -> assert false
  | Under (_, c) -> dive (n - 1) c

let rec compare c c' =
  match c, c' with
  | Root f, Root f' -> Expr.Formula.compare f f'
  | Under (f, d), Under (f', d') ->
    CCOrd.Infix.(Expr.Formula.compare f f'
                 <?> (compare, c, c'))
  | Root _, Under _ -> -1
  | Under _, Root _ -> 1

let cmp c c' =
  let d = depth c in
  let d' = depth c' in
  let a, b, inversed =
    if d < d' then c, c', false else c', c, true
  in
  let diff = abs (d - d') in
  let c = dive diff b in
  if compare a c = 0 then
    if diff = 0
    then Comparison.Eq
    else if inversed
    then Comparison.Gt
    else Comparison.Lt
  else Comparison.Incomparable

let mk_root f = Root f
let mk_cluster f c = Under (f, c)

(** Cluster registering *)
let tbl = Hf.create 4013

let get_cluster f =
  let q = match f with
    | { Expr.formula = Expr.All _ }
    | { Expr.formula = Expr.AllTy _ } -> f
    | { Expr.formula = Expr.Not ( {
        Expr.formula = Expr.(Ex _ | ExTy _) } as f' ) } -> f'
    | _ -> raise (Invalid_argument "Inst.get_cluster")
  in
  try Some (Hf.find tbl q)
  with Not_found -> None

let rec set_cluster c f =
  match f.Expr.formula with
  | Expr.Pred _
  | Expr.Equal _
  | Expr.True | Expr.False -> ()
  | Expr.Not f' -> set_cluster c f'
  | Expr.And l
  | Expr.Or l -> List.iter (set_cluster c) l
  | Expr.Imply (p, q)
  | Expr.Equiv (p, q) -> List.iter (set_cluster c) [p; q]
  | Expr.All (_, _, f')
  | Expr.AllTy (_, _, f')
  | Expr.Ex (_, _, f')
  | Expr.ExTy (_, _, f') -> Hf.add tbl f c; set_cluster c f'

let mark_meta quant f =
  match get_cluster quant with
  (* All/NotEx following AllTy/NotExTy should have the same cluster. *)
  | Some Root r when Expr.Formula.equal quant r -> ()
  (* General case *)
  | None -> set_cluster (mk_root f) f
  | Some c -> set_cluster (mk_cluster f c) f

(* Instanciation helpers *)
(* ************************************************************************ *)

(* TODO: cache cluster access for meta-variables *)

module N = CCMap.Make(CCInt)
module M = CCMap.Make(Expr.Formula)

(* Given a mapping, split it into mapping
   for which all metas have the same root cluster *)
let split m =
  let aux def bind m e acc =
    let f = def m.Expr.meta_index in
    let r = match get_cluster f with
      | Some c -> root c | None -> raise (Invalid_argument "Inst.split") in
    let s = M.get_or ~default:Mapping.empty r acc in
    M.add r (bind s m e) acc
  in
  let tmp =
    Mapping.fold m M.empty
      ~ty_var:(fun _ _ _ -> assert false)
      ~ty_meta:(aux Expr.Meta.ttype_def Mapping.Meta.bind_ty)
      ~term_var:(fun _ _ _ -> assert false)
      ~term_meta:(aux Expr.Meta.ty_def Mapping.Meta.bind_term)
  in
  M.fold (fun _ m acc -> m :: acc) tmp []

(* Find the miniaml cluster in a mapping where all meta definitions
   are supposed to be comparable (as is the case in theoutput of split). *)
let min_cluster mapping =
  let aux def m e acc =
    let f = def m.Expr.meta_index in
    match get_cluster f, acc with
    | Some c, None -> Some c
    | Some c, Some c' ->
      begin match cmp c c' with
        | Comparison.Lt -> Some c
        | Comparison.Incomparable ->
          Util.warn ~section "@[<hv 2>Non-comparable clusters in mapping@ %a@]"
            Mapping.print mapping;
          acc
        | _ -> acc
      end
    | None, _ ->
      Util.error ~section "Defining formula for meta %a doesn't have a cluster"
        Expr.Print.meta m;
      assert false
  in
  Mapping.fold mapping None
    ~ty_var:(fun _ _ _ -> assert false)
    ~ty_meta:(aux Expr.Meta.ttype_def)
    ~term_var:(fun _ _ _ -> assert false)
    ~term_meta:(aux Expr.Meta.ty_def)

(** Take a map, and filter out all metas but for the
    smallest cluster. *)
let reduce_map s =
  match min_cluster s with
  | None -> assert false
  | Some c ->
    let aux def m e =
      let f = def m.Expr.meta_index in
      match get_cluster f with
      | None -> assert false
      | Some c' -> compare c c' = 0
    in
    Mapping.filter s
      ~ty_var:(fun _ _ -> assert false)
      ~ty_meta:(aux Expr.Meta.ttype_def)
      ~term_var:(fun _ _ -> assert false)
      ~term_meta:(aux Expr.Meta.ty_def)

(** Split a single_cluster mapping according to meta indexes *)
let split_cluster map =
  let aux meta t acc =
    let i = (meta.Expr.meta_index : _ Expr.meta_index :> int) in
    let s = N.get_or ~default:Mapping.empty i acc in
    N.add i (Mapping.Meta.bind_term s meta t) acc
  in
  let tmp = Expr.Subst.fold aux (Mapping.term_meta map) N.empty in
  List.map snd (N.bindings tmp)

(** Returns the formula defining a mapping (where all metas
    are assumed to be defined by the same formula or contiguous
    quantifications (i.e same cluster). *)
let map_def map =
  try
    let m, _ = Expr.Subst.choose (Mapping.ty_meta map) in
    Expr.Meta.ttype_def m.Expr.meta_index
  with Not_found ->
    begin try
        let m, _ = Expr.Subst.choose (Mapping.term_meta map) in
        Expr.Meta.ty_def m.Expr.meta_index
      with Not_found ->
        raise (Invalid_argument "Inst.map_def")
    end

(* Given an arbitrary mapping,
 * returns a list of pairs (formula * mapping) to instanciate
 * the outermost metas in the given mapping. *)
let partition m =
  let l = split m in
  let l = List.map reduce_map l in
  CCList.flat_map split_cluster l

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof f q t =
  Dispatcher.mk_proof "inst" "partial" (Inst (Formula (f, t, q)))

let to_var s =
  Mapping.fold
    ~ty_var:(fun _ _ _ -> assert false)
    ~ty_meta:(fun {Expr.meta_id = v} t acc -> Mapping.Var.bind_ty acc v t)
    ~term_var:(fun _ _ _ -> assert false)
    ~term_meta:(fun {Expr.meta_id = v} t acc -> Mapping.Var.bind_term acc v t)
    s Mapping.empty

let soft_subst f t =
  let ty_subst = Mapping.ty_var t in
  let term_subst = Mapping.term_var t in
  let q = Expr.Formula.partial_inst ty_subst term_subst f in
  [ Expr.Formula.neg f; q], mk_proof f q t

(* Groundify substitutions *)
(* ************************************************************************ *)

type Expr.builtin +=
  | Ty_cst
  | Term_cst

let ty_cst =
  Expr.Ty.apply (Expr.Id.ty_fun ~builtin:Ty_cst "ty_cst" 0) []

let t_cst =
  let a = Expr.Id.ttype "a" in
  let f = Expr.Id.term_fun ~builtin:Term_cst
      "term_cst" [a] [] (Expr.Ty.of_id a) in
  (fun ty -> Expr.Term.apply f [ty] [])

let groundify m =
  let (tys, terms), _ = Mapping.codomain m in
  let s = List.fold_left (fun s v ->
      Mapping.Var.bind_term s v (t_cst Expr.(v.id_type))
    ) (List.fold_left (fun s v ->
      Mapping.Var.bind_ty s v ty_cst
    ) Mapping.empty tys) terms in
  Mapping.apply s m

(* Heap for prioritizing instanciations *)
(* ************************************************************************ *)

module Inst = struct
  type t = {
    age : int;
    hash : int;
    score : int;
    formula : Expr.formula;
    var_subst : Mapping.t;
  }

  (* Age counter *)
  let age = ref 0
  let clock () = incr age

  (* Constructor *)
  let mk u score =
    let formula = map_def u in
    let var_subst = to_var (groundify u) in
    let hash = Hashtbl.hash (Expr.Formula.hash formula, Mapping.hash u) in
    { age = !age; hash; score; formula; var_subst; }

  (* debug printing *)
  let print fmt t =
    Format.fprintf fmt "@[<hov 2>%a@ %a@]"
      Expr.Formula.print t.formula Mapping.print t.var_subst

  (* Comparison for the Heap *)
  let leq t1 t2 = t1.score + t1.age <= t2.score + t2.age

  (* Hash and equality for the hashtbl. *)
  let hash t = t.hash

  let equal t t' =
    Expr.Formula.equal t.formula t'.formula &&
    Mapping.equal t.var_subst t'.var_subst

end

module Q = CCHeap.Make(Inst)
module H = Hashtbl.Make(Inst)

let heap = ref Q.empty
let delayed = ref []
let inst_set = H.create 4096
let inst_incr = ref 0

let add ?(delay=0) ?(score=0) u =
  assert (match split_cluster (reduce_map u) with
      | [s] -> Mapping.equal s u
      | _ -> false);
  let t = Inst.mk u score in
  if not (H.mem inst_set t) then begin
    H.add inst_set t false;
    Util.debug ~section "New inst (%d):@ %a" delay Inst.print t;
    if delay <= 0 then
      heap := Q.add !heap t
    else
      delayed := (t, delay) :: !delayed;
    true
  end else begin
    Util.debug ~section "Redondant inst:@ %a" Inst.print t;
    false
  end

let push acc inst =
  assert (not (H.find inst_set inst));
  H.replace inst_set inst true;
  let open Inst in
  Util.debug ~section "Pushing inst:@ %a" Inst.print inst;
  let cl, p = soft_subst inst.formula inst.var_subst in
  Dispatcher.push cl p;
  acc + 1

let decr_delay () =
  if !delayed = [] then
    false
  else begin
    delayed := CCList.filter_map (fun (u, d) ->
        if d > 1 then begin
          Util.debug ~section "Decreased delay (%d):@ %a"
            (d - 1) Inst.print u;
          Some (u, d - 1)
        end else begin
          Util.debug ~section "Promoted inst:@ %a"
            Inst.print u;
          heap := Q.add !heap u;
          None
        end
      ) !delayed;
    true
  end

let inst_aux f acc k =
  let rec fold f acc i =
    if i <= 0 then
      if acc <= 0 && decr_delay () then
        fold f acc i
      else
        acc
    else begin
      match Q.take !heap with
      | None ->
        if decr_delay () then
          fold f acc i
        else
          fold f acc (i - 1)
      | Some (new_h, min) ->
        heap := new_h;
        fold f (f acc min) (i - 1)
    end
  in
  if k > 0 then begin
    Util.debug ~section "Folding over %d insts" k;
    fold f acc k
  end else begin
    Util.debug ~section "Folding over %d insts" (Q.size !heap + k);
    fold f acc (max 1 (Q.size !heap + k))
  end

let inst_sat () =
  Util.info ~section "Treating instanciations (k=%d)" !inst_incr;
  let n = inst_aux push 0 !inst_incr in
  Ext_stats.inst_remaining (Q.size !heap + List.length !delayed);
  Ext_stats.inst_done n;
  Inst.clock ();
  if n > 0 then
    Some (Solver.Assume [])
  else
    Some Solver.Sat_ok

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Formula (f, t, _) ->
    Some "RED", [
      CCFormat.const Dot.Print.mapping t;
      CCFormat.const Dot.Print.formula f;
    ]
(*
let coq_destruct ctx fmt = function
  | { Expr.formula = Expr.Not ({
      Expr.formula = Expr.Ex(l, _, _)} as q)} ->
    let o = Expr.L (List.rev @@ (Expr.F (`Quant q)) ::
                                List.rev_map (fun x -> Expr.F (`Var x)) l) in
    let pp fmt = function
      | `Var x -> Coq.Print.id fmt x
      | `Quant q -> Proof.Ctx.named ctx fmt q
    in
    Format.fprintf fmt "destruct %a as %a.@ "
      (Proof.Ctx.named ctx) q (Coq.Print.pattern_ex pp) o
  | _ -> ()

let coq_inst_ex m cur fmt x =
  let t = match Mapping.Var.get_term_opt m x with
    | None -> Expr.Term.of_id x
    | Some t -> t
  in
  Format.fprintf fmt
    "(Coq.Logic.Classical_Pred_Type.not_ex_all_not _ _ %s) %a"
    cur Coq.Print.term t

let coq_proof = function
  | Formula ({ Expr.formula = Expr.All (l, _, _) } as f, t, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f]) (fun fmt ctx ->
        let l', l'' = List.fold_left (fun (vars, args) x ->
            match Mapping.Var.get_term_opt t x with
            | None -> x :: vars, Expr.Term.of_id x :: args
            | Some t -> vars, t :: args) ([], []) l in
        let vars = List.rev l' in
        let args = List.rev l'' in
        begin match vars with
          | [] ->
            Coq.exact fmt "%a (%a)"
              (Proof.Ctx.named ctx) (Expr.Formula.neg q)
              (Coq.app_t ctx) (f, args)
          | _ ->
            Coq.exact fmt "%a (fun %a => %a)"
              (Proof.Ctx.named ctx) (Expr.Formula.neg q)
              Coq.fun_binder vars (Coq.app_t ctx) (f, args)
        end)
  | Formula ({ Expr.formula = Expr.Not (
      { Expr.formula = Expr.Ex (l, _, _) })} as f', t, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:Coq.All
      ~prelude:[Coq.Prelude.classical] (fun fmt ctx ->
        (** Destruct the goal *)
        let () = coq_destruct ctx fmt q in
        let s = Coq.sequence ctx (coq_inst_ex t) (Proof.Ctx.name ctx f') fmt l in
        Coq.exact fmt "%s %a" s (Proof.Ctx.named ctx) (Expr.Formula.neg q)
      )
  | _ -> assert false
*)
(* Extension registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Inst info -> Some (dot_info info)
  (* | Coq.Tactic Inst info -> Some (coq_proof info) *)
  | Solver.Found_sat _ -> inst_sat ()
  | _ -> None

let opts =
  let docs = Options.ext_sect in
  let n_of_inst =
    let doc = "Decides how many instanciations are pushed to the solver each round.
                   If $(docv) is a strictly positive number, then at each round, the $(docv)
                   most promising instanciations are pushed. If $(docv) is negative, then all
                   but the $(docv) least promising instanciations are pushed." in
    Cmdliner.Arg.(value & opt int 0 & info ["inst.nb"] ~docv:"N" ~docs ~doc)
  in
  let set_opts nb =
    inst_incr := nb
  in
  Cmdliner.Term.(pure set_opts $ n_of_inst)

let register () =
  Dispatcher.Plugin.register "inst" ~prio:5 ~options:opts
    ~descr:"Handles the pushing of clauses corresponding to instanciations. This plugin does not
          do anything by itself, but rather is called by other plugins when doing instanciations."
    (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle} ())

