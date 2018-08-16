
let section = Section.make "core"
let solver_section = Section.make "sat"
let plugin_section = Section.make ~parent:section "plugin"
let slice_section = Section.make ~parent:section "slice"

let dummy_section = Section.make "DUMMY"

(* Statistics *)
(* ************************************************************************ *)

let stats_watchers = Stats.mk "watchers"
let stats_conflicts = Stats.mk "conflicts"

let stats_pushed = Stats.mk "pushed"

let plugin_stats_group = Stats.bundle [
    stats_watchers;
    stats_conflicts;
    stats_pushed;
  ]

let stats_assignable = Stats.mk "var assignable"
let stats_evalable = Stats.mk "var eval-able"

let stats_evaluated = Stats.mk "formula evaluated"

let stats_assignments = Stats.mk "assignments"
let stats_evaluations = Stats.mk "evaluations"

let stats_group = Stats.bundle [
    stats_assignable;
    stats_assignments;

    stats_evalable;
    stats_evaluations;
    stats_evaluated;
  ]

let () = Stats.attach section stats_group

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
  mutable job_lvl : int;
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
  Stats.attach section plugin_stats_group;
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

let find_section name = Plugin.((find name).ext).section

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

let internal_plugin_id =
  let ext_name = "<internal>" in
  let () = Plugin.register ext_name ~prio:0
    ~descr:"Internal plugin for the dispatcher, do not disable..."
    (mk_ext ~section ()) in
  let () = Plugin.activate ext_name in
  Plugin.((find ext_name).id)

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  match Expr.Id.get_valuation v with
  | Expr.Assign _ -> Stats.incr stats_assignable section
  | Expr.Eval _ -> Stats.incr stats_evalable section
  | exception Exit ->
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

(* Current asusmptions *)
(* ************************************************************************ *)

let create = SolverTypes.add_atom

let eval_f f =
  let open SolverTypes in
  let a = create f in
  let lvl = a.var.v_level in
  let t =
    if a.is_true then Some true
    else if a.neg.is_true then Some false
    else None
  in
  t, lvl

let get_truth f = fst @@ eval_f f

let get_absolute_truth f =
  let truth, lvl = eval_f f in
  if lvl = 0 then truth else None

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* Exceptions *)
exception Not_assigned of Expr.term

(* The current assignment map, term -> level * value *)
let eval_map : (int * Expr.Term.t) B.t = B.create stack

(* Is a term assigned ? *)
let is_assigned t =
  try ignore (B.find eval_map t); true with Not_found -> false

(* Get the value assigned to a term *)
let get_assign t =
  try snd @@ B.find eval_map t with Not_found -> raise (Not_assigned t)

let get_assign_level t =
  try fst @@ B.find eval_map t with Not_found -> raise (Not_assigned t)


(* Dependency map for assignments, term -> term list.
   an empty list denotes no dependencies,
   a non-empty list signifies that the term is actually evaluated
   (and not assigned), but its vaue can be derived from the values
   of the terms in the list. *)
let eval_depends : Expr.Term.t list B.t = B.create stack

(** Compute the transitive closure of dependencies *)
let rec resolve_deps_aux t =
  match B.find eval_depends t with
  | [] -> [t]
  | l -> resolve_deps l
  | exception Not_found ->
    if is_assigned t then [t]
    else begin
      Util.error ~section
        "@[<hv>Resolving dependences of non-assigned lit:@ %a@]"
        Expr.Term.print t;
      assert false
    end

and resolve_deps l =
  CCList.flat_map resolve_deps_aux l


(* Map of jobs watched by each term *)
let watch_map : Plugin.id job list H.t = H.create 4096

(* A convenince function *)
let get_watched t =
  match H.find watch_map t with
  | exception Not_found -> []
  | res ->
    H.remove watch_map t;
    res

(** Add a job watched by [t] *)
let add_job job t =
  let l = try H.find watch_map t with Not_found -> [] in
  H.replace watch_map t (job :: l)


(** Jobs are queue in a trail before being called and executed.
    This is done for 2 reasons:
    - jobs may raise Absurd, thus in some contexts a watch can be registered,
      but it is unsafe to call the job (even if it shoul be called), thus enqueuing
      jobs offer a way to delay calling them until we are in an adequate context
    - some watchs may eb registered lately (i.e far after all the watched terms
      are assigned), in which case, if we backtrack to before the job was registered
      but after its watched terms are assigned, the job should be re-run.

    For each backtrack point recorded by mSAT, we thus store the length of
    the job trail, to knwo where to backtrack to.
*)
(** The index (in job_trail) of the first non-called job *)
let job_idx = ref 0
(** the trail of jobs (all jobs with index < !job_idx have been executed)*)
let job_trail = CCVector.create ()
(** A vector which stores at position [i] the length of the job trail at backtrack point i. *)
let job_level = CCVector.create ()

(* Enqueue a new job (without executing it) *)
let enqueue_job j lvl =
  if j.job_lvl >= 0 then ()
  else begin
    j.job_lvl <- lvl;
    CCVector.push job_trail j
  end

let current_assign_level () =
  CCVector.length job_level

let stack_assign_level () =
  let n = CCVector.length job_level in
  let () = CCVector.push job_level (current_assign_level ()) in
  n


(** Call/execute a single job *)
let call_job j =
  if not CCOpt.(get_or ~default:true (j.job_formula >>= get_truth)) then
    Util.debug ~section "Ignoring job because of false formula:@ %a"
      Expr.Formula.print (CCOpt.get_exn j.job_formula)
  else begin
    Util.debug ~section "Calling job from %s"
      Plugin.((get j.job_ext).name);
    profile j.job_section j.job_callback ()
  end

(* Call all jobs on the job trail.
   Executing jobs may : 1) raise Absurd
                        2) add new assignments/evluations,
                           and hence add new jobs on the trail
   In the loop, job_idx is incremented *after* calling the job
   in order to ensure that [!job_idx = CCVector.length job_trail]
   indicates that all jobs have run without raising Absurd.
*)
let do_all_jobs () =
  while !job_idx < CCVector.length job_trail do
    let j = CCVector.get job_trail !job_idx in
    let () = call_job j in
    job_idx := !job_idx + 1
  done

(* Backtrack the jobs
   There are two main tasks to perform:
   - reset job_lvl to -1 for undone jobs
   - re-call jobs that were called late and thus have a level
     lower (or equal) to the one we backtrack to. *)
let cancel_jobs lvl =
  let j_lvl = CCVector.get job_level lvl in
  let new_size = ref j_lvl in
  for i = j_lvl to CCVector.length job_trail - 1 do
    let j = CCVector.get job_trail i in
    if j.job_lvl > lvl then
      j.job_lvl <- -1
    else begin
      CCVector.set job_trail !new_size j;
      new_size := !new_size + 1
    end
  done;
  let () = CCVector.shrink job_trail !new_size in
  let () = CCVector.shrink job_level lvl in
  job_idx := j_lvl


(* Update watches for job [j] given that [x] has been assigned (and is
   in the watch set of the job). *)
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
      enqueue_job j (get_assign_level x);
      add_job j x
  with Not_found ->
    let ext = Plugin.get j.job_ext in
    Util.error ~section
      "Error for job from %s@ looking for %d, called by %a@\nwatched:@ @[<hov>%a@]@\nnot_watched:@ @[<hov>%a@]"
      ext.Plugin.name j.job_n Expr.Print.term x
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) j.watched
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) j.not_watched;
    assert false

(* Create a new job *)
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
    job_lvl = - 1;
  }

(* Add a new assignment, and if needed update watches (and maybe enqueue some jobs) *)
let set_assign t v =
  Util.enter_prof section;
  match B.find eval_map t with
  (* Term is already assigned, check that the values are equal. *)
  | _, v' ->
    Util.debug ~section "Assigned:@ @[<hov>%a ->@ %a@]@\nAssigning:@ @[<hov>%a ->@ %a@]"
      Expr.Print.term t Expr.Print.term v'
      Expr.Print.term t Expr.Print.term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments";
    Util.exit_prof section
  (* Term is not already assigned, update the watches. *)
  | exception Not_found ->
    Util.debug ~section "Assign:@ @[<hov>%a ->@ %a@]"
      Expr.Print.term t Expr.Print.term v;
    B.add eval_map t (current_assign_level (), v);
    let l = get_watched t in
    Util.debug ~section "Found %d watchers" (List.length l);
    let () = List.iter (update_watch t) l in
    Util.exit_prof section

(* watch fuction added to evaluate a term [t],
   using function [f], which itself need terms in [l] to be assigned.
   Since this is registered as a regular watch function, it will be called
   again if needed, so there is no need to compute the exact level of assignment
   for [t]. *)
let ensure_assign_aux t l f = (fun () ->
    Stats.incr stats_evaluations section;
    set_assign t (f ());
    B.add eval_depends t l
  )

(* Tag used to only register evaluation watchers once per term.
   NOTE: it only prevents watches from the same physical representation of terms
         (since terms are not hashconsed, two term with different tag sets can be equal),
         thus it mght be intersting to turn this into a hashtbl. *)
let eval_tag = Tag.create ()

(* Ensure that [t] will be gven a value at one point or another.
   There are two possibilities:
   - either [t] will be given a value (assigned)
   - or [t] will be evaluated using values for its subterms (in case of
     terms with an interpreted function at the top, such as [+(1,2)]).
     In this case, we must register a watcher to propagate the value for [t]
     once its subterms are assigned. *)
let rec ensure_assign t =
  if not Expr.(Ty.equal Ty.prop t.t_type) then
    match Expr.Term.valuation t with
    | Expr.Assign _ -> () (* Term will be assigned eventually *)
    | Expr.Eval k ->
      begin match Expr.Term.get_tag t eval_tag with
        | Some () -> ()
        | None ->
          let name, to_watch, f = k t in
          let plugin = Plugin.find name in
          let plugin_id = Plugin.(plugin.id) in
          let plugin_section = Plugin.(plugin.ext.section) in
          watch_aux plugin_section plugin_id 1 to_watch (ensure_assign_aux t to_watch f)
      end

(* Register a new watch function [f], watching [k] terms among [l].
   Watch functions are called once there are strictly less than [k]
   non-assigned terms among [l]. Usually [k = 1] or [k = 2].
*)
and watch_aux ?formula section plugin_id k args f =
  List.iter ensure_assign args;
  assert (k > 0);
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      let j = new_job ?formula plugin_id k section not_assigned (List.rev_append l assigned) f in
      List.iter (add_job j) not_assigned
    | [] (* i > 0 *) ->
      let lvls = List.map get_assign_level assigned in
      let lvl = List.fold_left max 0 lvls in
      let l = List.rev_append not_assigned assigned in
      let to_watch, not_watched = CCList.take_drop k l in
      let j = new_job ?formula plugin_id k section to_watch not_watched f in
      List.iter (add_job j) to_watch;
      enqueue_job j lvl
    | y :: r (* i > 0 *) ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  Util.debug ~section "Watch added";
  split [] [] k (List.sort_uniq Expr.Term.compare args)

(* Make a function to register new watches. This should be the only watch function
   exposed in the public interface.
   It takes a module as argument in order to provide function that can avoid
   registering watches with the same key twice (and make that key type polymorphic).
*)
and mk_watch (type t) (module A : Hashtbl.HashedType with type t = t) ext_name =
  let module H = Hashtbl.Make(A) in
  let h = H.create 4013 in
  (fun ?formula key k args f ->
     let plugin = Plugin.find ext_name in
     let section = Plugin.(plugin.ext.section) in
     let tag = Plugin.(plugin.id) in
     Util.debug ~section "New watch from %s, %d among:@ @[<hov>%a@]"
       Plugin.((get tag).name) k
       CCFormat.(list ~sep:(return " ||@ ") Expr.Print.term) args;
     if H.mem h key then
       Util.debug ~section "redundant watch"
     else begin
       H.add h key ();
       watch_aux ?formula section tag k args f
     end
  )

(* Return a snapshot of the current model *)
let model () =
  let h = B.H.create 4013 in
  let () = B.iter (fun key (_, v) -> B.H.add h key v) eval_map in
  h

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
    Stats.incr stats_pushed (find_section p.plugin_name);
    Util.debug ~section:slice_section "New clause to push (%s):@ @[<hov>%a@]"
      p.proof_name
      CCFormat.(list ~sep:(return " ||@ ") Expr.Print.formula) clause;
    Stack.push (clause, p) push_stack
  end

let consequence f l p =
  Stack.push (f, Msat.Plugin_intf.Consequence (l, p)) propagate_stack

let propagate f l =
  Stats.incr stats_evaluated section;
  Util.debug ~section "@[<hv>Propagating@ %a@ because of@ %a@]"
    Expr.Formula.print f CCFormat.(list ~sep:(return ",@ ") Expr.Term.print) l;
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

  type level = int * Backtrack.Stack.level

  let dummy = -1, Backtrack.Stack.dummy_level

  let current_level () =
    stack_assign_level (), Backtrack.Stack.level stack

  let backtrack (j_lvl, lvl) =
    Util.debug ~section:slice_section "Backtracking";
    let () = Stack.clear propagate_stack in
    let () = Backtrack.Stack.backtrack stack lvl in
    let () = cancel_jobs j_lvl in
    ()

  let assume s =
    let open Msat.Plugin_intf in
    Util.enter_prof section;
    Util.debug ~section:slice_section "New slice of length %d" s.length;
    try
      Util.debug ~section "Performing enqueued jobs";
      let () = do_all_jobs () in
      let assume_aux = plugin_assume () in
      for i = s.start to s.start + s.length - 1 do
        match s.get i with
        | Lit f ->
          Util.debug ~section:slice_section "assuming:@ @[<hov>%a@]"
            Expr.Print.formula f;
          assume_aux f
        | Assign (t, v) ->
          Stats.incr stats_assignments section;
          Util.debug ~section:slice_section "assuming: @[<hov>%a ->@ %a@]"
            Expr.Print.term t Expr.Print.term v;
          set_assign t v
      done;
      Util.debug ~section "Perfoming enqueued jobs";
      let () = do_all_jobs () in
      do_propagate s.propagate;
      do_push s.push;
      Util.exit_prof section;
      Sat
    with Absurd (l, p) ->
      Stats.incr stats_conflicts (find_section p.plugin_name);
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
      Util.exit_prof section;
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
      Stats.incr stats_conflicts (find_section p.plugin_name);
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
      Stats.incr stats_evaluated section;
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
