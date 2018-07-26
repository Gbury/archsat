
let section = Section.make "core"
let solver_section = Section.make "sat"
let plugin_section = Section.make ~parent:section "plugin"
let slice_section = Section.make ~parent:section "slice"

let dummy_section = Section.make "DUMMY"

(* Statistics *)
(* ************************************************************************ *)

let stats_watchers = Stats.mk "watchers"

let stats_group = Stats.bundle [stats_watchers]

(* Type definitions *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)
module B = Backtrack.Hashtbl(Expr.Term)
module F = Backtrack.Hashtbl(Expr.Formula)

module M = B.H

type lemma_info = ..

type lemma = {
  id : int;
  plugin_name : string;
  proof_name  : string;
  proof_info  : lemma_info;
}

type 'a job = {
  job_ext : 'a;
  job_n : int;
  job_section : Section.t;
  job_callback : unit -> unit;
  job_formula : Expr.formula option;
  mutable job_done : int;
  mutable watched : Expr.term list;
  mutable not_watched : Expr.term list;
}

(* Solver types *)
(* ************************************************************************ *)

module SolverExpr = struct

  module Term = Expr.Term

  module Formula = struct
    include Expr.Formula

    let neg f = Expr.Formula.neg f

    let norm = function
      | { Expr.formula = Expr.False } ->
        Expr.Formula.f_true, Msat.Expr_intf.Negated
      | { Expr.formula = Expr.Not f } ->
        f, Msat.Expr_intf.Negated
      | f ->
        f, Msat.Expr_intf.Same_sign

    let dummy = Expr.Formula.f_true
  end

  type proof = lemma
end


module SolverTypes = Msat.Solver_types.McMake(SolverExpr)()

(* Exceptions *)
(* ************************************************************************ *)

exception Bad_assertion of string
exception Absurd of Expr.formula list * lemma

let _fail s = raise (Bad_assertion s)

let profile section f = fun x ->
  Util.enter_prof section;
  try
    let res = f x in
    Util.exit_prof section;
    res
  with Absurd _ as e ->
    Util.exit_prof section;
    raise e

(* Messages for extensions *)
(* ************************************************************************ *)

type 'ret msg = ..
type 'ret msg +=
  | If_sat : ((Expr.formula -> unit) -> unit) -> unit msg

type handle = {
  handle : 'ret. 'ret msg -> 'ret option;
}

(* Extensions *)
(* ************************************************************************ *)

type ext = {
  (* Section for the extension (used for profiling) *)
  section : Section.t;

  (* Setup handlers (called once on each formula) *)
  set_handler : (Expr.formula -> unit) option;

  (* Setup watches (called ocne on each formula) *)
  set_watcher : (Expr.formula -> unit) option;

  (* Called on each formula that the solver assigns to true *)
  assume : (Expr.formula -> unit) option;

  (* Evaluate a formula with the current assignments *)
  eval_pred : (Expr.formula -> (bool * Expr.term list) option) option;

  (* Handle messages *)
  handle : 'ret 'acc. (
      ('acc -> 'ret option -> 'acc) -> 'acc -> 'ret msg -> 'acc
    ) option;

  (* Pre-process input formulas *)
  preprocess : (Expr.formula -> (Expr.formula * lemma) option) option;
}

let mk_ext
    ~section ?(handle: handle option)
    ?set_handler ?set_watcher ?assume ?eval_pred ?preprocess () =
  Stats.attach section stats_group;
  {
    section;
    set_handler = CCOpt.map (profile section) set_handler;
    set_watcher = CCOpt.map (profile section) set_watcher;
    assume = CCOpt.map (profile section) assume;
    eval_pred = CCOpt.map (profile section) eval_pred;
    preprocess = CCOpt.map (profile section) preprocess;
    handle = match handle with
      | None -> None
      | Some h ->
        Some (fun (type acc) (type ret)
               (fold : acc -> ret option -> acc)
               (acc: acc) (msg : ret msg) ->
               fold acc (profile section h.handle msg)
             );
  }

let merge_opt merge o1 o2 = match o1, o2 with
  | None, res | res, None -> res
  | Some a, Some b -> Some (merge a b)

(* merge: iter on functions *)
let merge_iter a b = merge_opt (fun f f' -> (function arg -> f arg; f' arg)) a b

(* merge: eval functions and stop on the first non-None result *)
let merge_first a b =
  merge_opt (fun f f' ->
      (function arg ->
       match f arg with
       | (Some _) as res -> res
       | None -> f' arg
      )) a b

let merge_preprocess f p =
  match f, p with
  | None, res | res, None -> res
  | Some f', Some p' ->
    Some (function formula -> match f' formula with
        | None -> p' formula
        | Some (formula', _) -> p' formula')

let merge_exts ~high ~low =
  {
    section = dummy_section;
    set_handler = merge_iter high.set_handler low.set_handler;
    set_watcher = merge_iter high.set_watcher low.set_watcher;
    assume = merge_iter high.assume low.assume;
    eval_pred = merge_first high.eval_pred low.eval_pred;
    preprocess = merge_preprocess high.preprocess low.preprocess;
    handle = begin match high.handle, low.handle with
      | None, res | res, None -> res
      | Some h, Some h' ->
        Some (fun (type acc) (type ret)
               (fold : acc -> ret option -> acc)
               (acc: acc) (msg : ret msg)
               ->
                 let acc' = h fold acc msg in
                 h' fold acc' msg
             )
    end;
  }

module Plugin = Extension.Make(struct
    type t = ext
    let neutral = mk_ext ~section ()
    let merge = merge_exts
    let section = plugin_section
  end)

let plugin_peek f =
  Util.debug ~section "Setting up handlers...";
  begin
    match (Plugin.get_res ()).set_handler with
    | Some h -> h f
    | None -> ()
  end;
  Util.debug ~section "Setting up watchers...";
  match (Plugin.get_res ()).set_watcher with
  | Some w -> w f
  | None -> ()

let plugin_preprocess f =
  match (Plugin.get_res ()).preprocess with
  | Some p -> p f
  | None -> None

let plugin_assume () =
  match (Plugin.get_res ()).assume with
  | Some assume -> assume
  | None -> (fun _ -> ())

let plugin_handle fold acc msg =
  match (Plugin.get_res ()).handle with
  | Some handle -> handle fold acc msg
  | None -> acc

let plugin_eval_pred f =
  match (Plugin.get_res ()).eval_pred with
  | Some eval_pred -> eval_pred f
  | None -> None

(* Sending messages *)
(* ************************************************************************ *)

let handle = plugin_handle

let send = plugin_handle (fun () _ -> ()) ()

let ask name msg =
  let ext = Plugin.find name in
  let aux = function
    | None -> (fun x -> x)
    | Some _ -> assert false
  in
  match ext.Plugin.ext.handle with
  | Some h -> h aux None msg
  | None ->
    Util.warn ~section "Plugin %s has no handle for incoming messages" name;
    None

(* Proof management *)
(* ************************************************************************ *)

let mk_proof =
  let r = ref 0 in
  (fun plugin_name proof_name proof_info ->
     let () = incr r in
     { id = !r; plugin_name; proof_name; proof_info; }
  )

(** Evaluation at level 0,
    TODO: implement proof generation (using rewriting ?),
          CAUTION: dependency problems for proofs (the handle
          should catch Proof.Lemma, but Proof depends on th dispatcher
          because it defines a new message, :/ ) *)
type lemma_info += Eval0

let () =
  let ext_name = "<internal>" in
  let () = Plugin.register ext_name ~prio:0
    ~descr:"Internal plugin for the dispatcher, do not disable..."
    (mk_ext ~section ()) in
  let () = Plugin.activate ext_name in
  ()

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  if not (Expr.Id.is_valuated v) then
    Util.warn ~section "WARNING: Variable '%a' has no valuation" Expr.Print.id v

let rec check_term = function
  | { Expr.term = Expr.Var v } -> check_var v
  | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_id)
  | { Expr.term = Expr.App (p, _, l)} as t ->
    if not (Expr.(Ty.equal t.t_type Ty.prop)) then check_var p;
    List.iter check_term l

let check = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    check_term a;
    check_term b
  | { Expr.formula = Expr.Pred p } ->
    check_term p
  | _ -> ()

let peek_at f =
  plugin_peek f;
  check f

let rec pre_process_aux acc f =
  match plugin_preprocess f with
  | None ->
    Util.debug ~section "Pre-processing (idem):@ @[<hov>%a@]"
      Expr.Print.formula f;
    f, List.rev acc
  | Some (f', lemma) ->
    Util.debug ~section "@[<hov>Pre-processing (changes): %a@ --->%a@]"
      Expr.Print.formula f Expr.Print.formula f';
    pre_process_aux (lemma :: acc) f'

let pre_process f =
  Util.enter_prof section;
  let f', _ = pre_process_aux [] f in
  Util.exit_prof section;
  f'

(* Backtracking *)
(* ************************************************************************ *)

let stack = Backtrack.Stack.create (
    Section.make ~parent:section "backtrack")

let last_backtrack = ref 0

(* Current asusmptions *)
(* ************************************************************************ *)

let create = SolverTypes.add_atom

let eval_f f =
  let open SolverTypes in
  let a = create f in
  if a.is_true then Some true
  else if a.neg.is_true then Some false
  else None

let get_truth = eval_f

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The current assignment map, term -> value *)
let eval_map = B.create stack
(* Dependency map for assignments, term -> term list.
   an empty list denotes no dependencies,
   a non-empty list signifies that the term is actually evaluated
   (and not assigned), but its vaue can be derived from the values
   of the terms in the list. *)
let eval_depends = B.create stack
(* Map of terms watched by extensions *)
let watchers = H.create 4096
let watch_map = H.create 4096

(* Exceptions *)
exception Not_assigned of Expr.term

(* Convenience function *)
let hpop assoc key =
  let res = H.find assoc key in
  H.remove assoc key;
  res

let is_assigned t =
  try ignore (B.find eval_map t); true with Not_found -> false

let get_assign t =
  try B.find eval_map t with Not_found -> raise (Not_assigned t)

let rec resolve_deps_aux t =
  match B.find eval_depends t with
  | [] -> [t]
  | l -> resolve_deps l
  | exception Not_found -> assert (is_assigned t); [t]

and resolve_deps l =
  CCList.flat_map resolve_deps_aux l

let add_job job t =
  let l = try H.find watch_map t with Not_found -> [] in
  H.replace watch_map t (job :: l)

let call_job j =
  if not CCOpt.(get_or ~default:true (j.job_formula >>= eval_f)) then
    Util.debug ~section "Ignoring job because of false formula:@ %a"
      Expr.Formula.print (CCOpt.get_exn j.job_formula)
  else if j.job_done >= !last_backtrack then
    Util.debug ~section
      "Ignoring job because it has already been executed since the last backtrack"
  else begin
    Util.debug ~section "Calling job from %s"
      Plugin.((get j.job_ext).name);
    j.job_done <- !last_backtrack;
    profile j.job_section j.job_callback ()
  end

let update_watch x j =
  let rec find p acc = function
    | [] -> raise Not_found
    | y :: r when p y -> y, List.rev_append r acc
    | y :: r -> find p (y :: acc) r
  in
  try
    let _, old_watched = find (Expr.Term.equal x) [] j.watched in
    try
      let y, old_not_watched = find (fun y -> not (is_assigned y)) [] j.not_watched in
      Util.debug ~section "New watcher for job from %s:@ @[<hov>%a@]"
        Plugin.((get j.job_ext).name) Expr.Print.term y;
      j.not_watched <- x :: old_not_watched;
      j.watched <- y :: old_watched;
      add_job j y
    with Not_found ->
      add_job j x;
      call_job j
  with Not_found ->
    let ext = Plugin.get j.job_ext in
    Util.error ~section
      "Error for job from %s@ looking for %d, called by %a@\nwatched:@ @[<hov>%a@]@\nnot_watched:@ @[<hov>%a@]"
      ext.Plugin.name j.job_n Expr.Print.term x
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) j.watched
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) j.not_watched;
    assert false

let new_job ?formula id k section watched not_watched f =
  Stats.incr stats_watchers section;
  {
    job_ext = id;
    job_n = k;
    job_section = section;
    watched = watched;
    job_formula = formula;
    not_watched = not_watched;
    job_callback = f;
    job_done = - 1;
  }

let rec assign_watch t = function
  | [] -> Util.exit_prof section
  | j :: r ->
    begin
      try
        update_watch t j
      with Absurd _ as e ->
        List.iter (fun job -> add_job job t) r;
        Util.exit_prof section;
        raise e
    end;
    assign_watch t r

and set_assign t v =
  Util.enter_prof section;
  try
    let v' = B.find eval_map t in
    Util.debug ~section "Assigned:@ @[<hov>%a ->@ %a@]@\nAssigning:@ @[<hov>%a ->@ %a@]"
      Expr.Print.term t Expr.Print.term v'
      Expr.Print.term t Expr.Print.term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments";
    Util.exit_prof section
  with Not_found ->
    Util.debug ~section "Assign:@ @[<hov>%a ->@ %a@]"
      Expr.Print.term t Expr.Print.term v;
    B.add eval_map t v;
    let l = try hpop watch_map t with Not_found -> [] in
    Util.debug ~section "Found %d watchers" (List.length l);
    assign_watch t l

let ensure_assign_aux t l f = (fun () ->
    set_assign t (f ());
    B.add eval_depends t l
  )

let eval_tag = Tag.create ()

let rec ensure_assign t =
  if not Expr.(Ty.equal Ty.prop t.t_type) then
    match Expr.Term.valuation t with
    | Expr.Assign _ -> () (* Term will be assigned eventually *)
    | Expr.Eval k ->
      begin match Expr.Term.get_tag t eval_tag with
        | Some () -> ()
        | None ->
          let ext_name, to_watch, f = k t in
          watch_aux ~force:true ext_name 1 to_watch (ensure_assign_aux t to_watch f)
      end

(* TODO: protect watch against raised exceptions during job calling.
         -> the "watch" function can actually raise Absurd since it can
            call the job if conditions are met, but since thre are recursive
            calls to it (due to ensure_assign),
            1) some watches may be lost becasue of the exception
            2) it may raise outside of the "assume" exception trap,
               particularly during the set_watchers phase, which would be problematic
   TODO: watchers with an empty list are called immediately, and thus their effect
         may be forgotten when backtracking. This may happen particularly for evaluators
         of expressions that are introduced lately (e.g. expressions created for conflicts).
*)

and watch_aux ~force ?formula ext_name k args f =
  let plugin = Plugin.find ext_name in
  let section = Plugin.(plugin.ext.section) in
  let tag = Plugin.(plugin.id) in
  List.iter ensure_assign args;
  assert (k > 0);
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      let j = new_job ?formula tag k section not_assigned (List.rev_append l assigned) f in
      List.iter (add_job j) not_assigned
    | [] (* i > 0 *) ->
      let l = List.rev_append not_assigned assigned in
      let to_watch, not_watched = CCList.take_drop k l in
      let j = new_job ?formula tag k section to_watch not_watched f in
      List.iter (add_job j) to_watch;
      call_job j
    | y :: r (* i > 0 *) ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  let t' = Builtin.Misc.tuple args in
  let l = try H.find watchers t' with Not_found -> [] in
  Util.debug ~section "New watch from %s, %d among:@ @[<hov>%a@]"
    Plugin.((get tag).name) k
    CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) args;
  if force || not (List.mem tag l) then begin
    Util.debug ~section "Watch added";
    H.add watchers t' (tag :: l);
    split [] [] k (List.sort_uniq Expr.Term.compare args)
  end else
    Util.debug ~section "Redundant watch"

let watch = watch_aux ~force:false

let model () = B.snapshot eval_map

(* Delayed propagation *)
(* ************************************************************************ *)

let push_stack = Stack.create ()
let propagate_stack = Stack.create ()

let push clause p =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) clause then
    Util.debug ~section:slice_section "Ignoring trivial new clause (%s):@ @[<hov>%a@]"
      p.proof_name
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) clause
  else begin
    Util.debug ~section:slice_section "New clause to push (%s):@ @[<hov>%a@]"
      p.proof_name
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) clause;
    Stack.push (clause, p) push_stack
  end

let consequence f l p =
  Stack.push (f, Msat.Plugin_intf.Consequence (l, p)) propagate_stack

let propagate f l =
  match resolve_deps l with
  | [] -> consequence f [] (mk_proof "" "eval0" Eval0)
  | l' -> Stack.push (f, Msat.Plugin_intf.Eval l') propagate_stack

let do_propagate propagate =
  while not (Stack.is_empty propagate_stack) do
    let (t, reason) = Stack.pop propagate_stack in
    Util.debug ~section:slice_section "Propagating to sat:@ @[<hov>%a@]" Expr.Print.formula t;
    propagate t reason
  done

let clean_propagate () =
  Stack.clear propagate_stack

let do_push f =
  while not (Stack.is_empty push_stack) do
    let (a, p) = Stack.pop push_stack in
    Util.debug ~section:slice_section "Pushing '%s':@ @[<hov>%a@]"
      p.proof_name
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) a;
    f a p
  done

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

module SolverTheory = struct

  type term = Expr.term
  type formula = Expr.formula

  type proof = lemma

  type level = Backtrack.Stack.level

  let dummy = Backtrack.Stack.dummy_level

  let current_level () = Backtrack.Stack.level stack

  let backtrack lvl =
    Util.debug ~section:slice_section "Backtracking";
    incr last_backtrack;
    Stack.clear propagate_stack;
    Backtrack.Stack.backtrack stack lvl

  let assume s =
    let open Msat.Plugin_intf in
    Util.enter_prof section;
    Util.debug ~section:slice_section "New slice of length %d" s.length;
    try
      let assume_aux = plugin_assume () in
      for i = s.start to s.start + s.length - 1 do
        match s.get i with
        | Lit f ->
          Util.debug ~section:slice_section "assuming:@ @[<hov>%a@]"
            Expr.Print.formula f;
          assume_aux f
        | Assign (t, v) ->
          Util.debug ~section:slice_section "assuming: @[<hov>%a ->@ %a@]"
            Expr.Print.term t Expr.Print.term v;
          set_assign t v
      done;
      Util.exit_prof section;
      do_propagate s.propagate;
      do_push s.push;
      Sat
    with Absurd (l, p) ->
      Util.exit_prof section;
      (* Propagating is important for literals true because of assignments at
         level 0 (which if not propagated, cannot be "evaluated" at level 0,
         and thus would render some conflicts invalid). However, since it can happen
         to new literals (that have not yet been "peeked", and thus not watched),
         we have to first ensure these literals exist in the SAT.
      *)
      let _ = List.map create l in
      do_propagate s.propagate;
      (* Debug and return value *)
      Util.debug ~section:slice_section "Conflict(%s):@ @[<hov>%a@]"
        p.proof_name CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) l;
      Unsat (l, p)

  let if_sat_iter s f =
    let open Msat.Plugin_intf in
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit g -> f g
      | _ -> ()
    done

  let if_sat s =
    Util.enter_prof section;
    Util.debug ~section "Final SAT check";
    try
      send (If_sat (if_sat_iter s));
      assert (Stack.is_empty propagate_stack);
      do_push s.Msat.Plugin_intf.push;
      Util.exit_prof section;
      Msat.Plugin_intf.Sat
    with Absurd (l, p) ->
      clean_propagate ();
      Util.debug ~section "Conflict(%s):@ @[<hov>%a@]"
        p.proof_name CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) l;
      Util.exit_prof section;
      Msat.Plugin_intf.Unsat (l, p)

  let assign t =
    Util.enter_prof section;
    Util.debug ~section "Finding assignment for:@ @[<hov>%a@]"
      Expr.Print.term t;
    try
      let res =
        match Expr.Term.valuation t with
        | Expr.Assign f -> f t
        | Expr.Eval _ -> raise (Expr.Cannot_valuate t)
      in
      Util.debug ~section "%a ->@ @[<hov>%a@]"
        Expr.Print.term t Expr.Print.term res;
      Util.exit_prof section;
      res
    with Expr.Cannot_valuate _ ->
      _fail (
        Format.asprintf
          "Expected to be able to assign term %a\nYou may have forgotten to activate an extension"
          Expr.Print.term t)

  let rec iter_assign_aux f e =
    match Expr.(e.term) with
    | Expr.Var _ -> assert false
    | Expr.App (p, _, l) ->
      if Expr.Id.is_assignable p &&
         not (Expr.Ty.equal Expr.Ty.prop e.Expr.t_type) then begin
        Util.debug ~section "mark as assignable: @[<hov>%a@]" Expr.Term.print e;
        f e
      end;
      List.iter (iter_assign_aux f) l
    | _ -> f e

  let iter_assignable f e =
    Util.enter_prof section;
    Util.debug ~section "Iter_assign on:@ %a" Expr.Print.formula e;
    peek_at e;
    begin match Expr.(e.formula) with
      | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
      | Expr.Pred p -> iter_assign_aux f p
      | _ -> ()
    end;
    Util.exit_prof section

  let print_eval_res fmt = function
    | Msat.Plugin_intf.Unknown ->
      Format.fprintf fmt "<unknown>"
    | Msat.Plugin_intf.Valued (b, l) ->
      Format.fprintf fmt "%B@ @[<hov 1>(%a)@]" b (CCFormat.list Expr.Print.term) l

  let eval_aux f =
    match plugin_eval_pred f with
    | None -> Msat.Plugin_intf.Unknown
    | Some (b, l) ->
      begin match resolve_deps l with
        (* Propagations at level 0 are actually forbidden currently,
           so instead we propagate it (the assume function takes care of
           doing these propagations before sending the conflit to msat). *)
        | [] ->
          let f' = if b then f else Expr.Formula.neg f in
          let () = propagate f' [] in
          Msat.Plugin_intf.Unknown
        (* Normal case: propagations at level > 0 *)
        | l' ->
          Msat.Plugin_intf.Valued (b, l')
      end

  let eval formula =
    Util.enter_prof section;
    Util.debug ~section "Evaluating formula:@ %a" Expr.Print.formula formula;
    let res = eval_aux formula in
    Util.debug ~section "Eval res:@ @[<hov>%a@]" print_eval_res res;
    Util.exit_prof section;
    res

end
