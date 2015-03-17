
let log_section = Util.Section.make "dispatch"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)
module M = Backtrack.HashtblBack(Expr.Term)
module I = Backtrack.HashtblBack(struct type t = int let equal i j = i=j let hash i = i land max_int end)

type id = int
type term = Expr.term
type formula = Expr.formula
type lemma = {
  proof_ext : id;
  proof_name : string;
  proof_ty_args : Expr.ty list;
  proof_term_args : Expr.term list;
  proof_formula_args : Expr.formula list;
}
type proof = lemma

type assumption =
  | Lit of formula
  | Assign of term * term

type slice = {
  start : int;
  length : int;
  get : int -> assumption * int;
  push : formula list -> proof -> unit;
  propagate : formula -> int -> unit;
}

type level = Backtrack.Stack.level

type res =
  | Sat
  | Unsat of formula list * proof

type eval_res =
  | Valued of bool * int
  | Unknown

type job = {
  job_ext : id;
  job_n : int;
  mutable job_done : int;
  job_callback : unit -> unit;
  mutable watched : term list;
  mutable not_watched : term list;
}

(* Proof management *)
(* ************************************************************************ *)

let mk_proof ?(ty_args=[]) ?(term_args=[]) ?(formula_args=[]) id name = {
  proof_ext = id;
  proof_name = name;
  proof_ty_args = ty_args;
  proof_term_args = term_args;
  proof_formula_args = formula_args;
}

let proof_debug p =
  let color = match p.proof_name with
    | "inst" -> Some "PURPLE"
    | "tab" -> Some "LIGHTBLUE"
    | _ -> None
  in
  p.proof_name, p.proof_formula_args, p.proof_term_args, color

(* Extensions registering *)
(* ************************************************************************ *)

exception Absurd of formula list * proof
exception Bad_assertion of string
exception Extension_not_found of string

let _fail s = raise (Bad_assertion s)

let new_id =
  let i = ref 0 in
  (fun () -> incr i; !i)

type extension = {
  id : id;
  prio : int;
  name : string;
  descr : string;
  if_sat : unit -> unit;
  assume : formula * int -> unit;
  eval_pred : formula -> (bool * int) option;
  preprocess : formula -> unit;
  options : Options.copts Cmdliner.Term.t -> Options.copts Cmdliner.Term.t;
}

let mk_ext ?(descr="")?(prio=0) ?(if_sat=(fun () -> ()))
    ?(assume=(fun _ -> ())) ?(eval_pred=(fun _ -> None))
    ?(preprocess=(fun _ -> ())) ?(options=(fun t -> t)) id name =
  { id; prio; name; descr; if_sat; assume; eval_pred; preprocess; options }

let extensions = ref []

let active = ref []

let register r =
  assert (not (List.exists (fun r' -> r'.name = r.name) !extensions));
  extensions := r :: !extensions

let activate ext =
  let aux r = r.name = ext in
  try
    let r = List.find aux !extensions in
    if not (List.exists aux !active) then
      active := List.merge (fun r r' -> compare r'.prio r.prio) [r] !active
    else
      log 0 "WARNING: Extension %s already activated" ext
  with Not_found ->
    raise (Extension_not_found ext)

let deactivate ext =
  let aux r = r.name = ext in
  try
    if not (List.exists aux !extensions) then
      raise (Extension_not_found ext);
    let l1, l2 = List.partition aux !active in
    begin match l1 with
      | [] -> log 0 "WARNING: Extension %s already deactivated" ext
      | [r] -> active := l2
      | _ -> assert false
    end
  with Not_found ->
    raise (Extension_not_found ext)

let set_ext s =
  match s.[0] with
  | '-' -> deactivate (String.sub s 1 (String.length s - 1))
  | '+' -> activate (String.sub s 1 (String.length s - 1))
  | _ -> activate s

let set_exts s = List.iter set_ext (Util.str_split ~by:"," s)


(* Info about extensions *)
let list_extensions () = List.map (fun r -> r.name) !extensions

let doc_of_ext r = `I ("$(b," ^ r.name ^ ")", r.descr)

let ext_doc () = List.map doc_of_ext
    (List.sort (fun r r' -> compare r.name r'.name) !extensions)

let find_ext id =
  List.find (fun ext -> ext.id = id) !extensions

let ext_iter f = List.iter f !active

(* Additional command line options *)
(* ************************************************************************ *)

let add_opts t =
  let res = ref t in
  List.iter (fun r ->
      res := r.options !res
    ) !extensions;
  !res

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  if not (Expr.is_interpreted v) && not (Expr.is_assignable v) then
    log 0 "WARNING: Variable %a is neither interpreted nor assignable" Expr.debug_var v

let rec check_term = function
  | { Expr.term = Expr.Var v } -> check_var v
  | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_var)
  | { Expr.term = Expr.App (p, _, l)} ->
    check_var p;
    List.iter check_term l

let rec check = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    check_term a;
    check_term b
  | { Expr.formula = Expr.Pred p } ->
    check_term p
  | { Expr.formula = ( Expr.True | Expr.False ) } ->
    ()
  | { Expr.formula = Expr.Not f } ->
    check f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter check l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    check p;
    check q
  | { Expr.formula = Expr.All (_, _, f) }
  | { Expr.formula = Expr.AllTy (_, _, f) }
  | { Expr.formula = Expr.Ex (_, _, f) }
  | { Expr.formula = Expr.ExTy (_, _, f) } ->
    check f

let preprocess f = ext_iter (fun r -> r.preprocess f); check f

(* Delayed propagation *)
(* ************************************************************************ *)

let push_stack = Stack.create ()
let propagate_stack = Stack.create ()

let push clause ext_name =
  Stack.push (clause, ext_name) push_stack

let propagate f lvl =
  Stack.push (f, lvl) propagate_stack

let do_propagate propagate =
  while not (Stack.is_empty propagate_stack) do
    let (t, lvl) = Stack.pop propagate_stack in
    log 10 "Propagating : %a" Expr.debug_formula t;
    propagate t lvl
  done

let do_push f =
  while not (Stack.is_empty push_stack) do
    let (a, p) = Stack.pop push_stack in
    log 2 "Pushing '%s' : %a" p.proof_name (Util.pp_list ~sep:" || " Expr.debug_formula) a;
    f a p
  done

(* Backtracking *)
(* ************************************************************************ *)

let stack = Backtrack.Stack.create ()

let dummy = Backtrack.Stack.dummy_level

let last_backtrack = ref 0

let current_level () = Backtrack.Stack.level stack

let backtrack lvl =
  log 10 "Backtracking";
  incr last_backtrack;
  Stack.clear propagate_stack;
  Backtrack.Stack.backtrack stack lvl

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The current assignment map, term -> value *)
let eval_map = M.create stack
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = M.create stack
(* Map of terms watched by extensions *)
let watchers = H.create 4096
let watch_map = H.create 4096

(* Exceptions *)
exception Not_assigned of term

(* Convenience function *)
let hpop assoc key =
  let res = H.find assoc key in
  H.remove assoc key;
  res

let is_assigned t =
  try ignore (M.find eval_map t); true with Not_found -> false

let get_assign t =
  try M.find eval_map t with Not_found -> raise (Not_assigned t)

(*
let add_wait_eval t t' =
  assert (not (is_assigned t));
  let l = try M.find wait_eval t' with Not_found -> [] in
  M.add wait_eval t' (List.sort_uniq Expr.Term.compare (t :: l))
*)

let add_job job t =
  let l = try H.find watch_map t with Not_found -> [] in
  H.replace watch_map t (job :: l)

let call_job j =
  if j.job_done < !last_backtrack then begin
    j.job_done <- !last_backtrack;
    j.job_callback ()
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
      log 10 "New watcher (%a) for job from %s" Expr.debug_term y (find_ext j.job_ext).name;
      j.not_watched <- x :: old_not_watched;
      j.watched <- y :: old_watched;
      add_job j y
    with Not_found ->
      add_job j x;
      log 10 "Calling job from %s" (find_ext j.job_ext).name;
      call_job j
  with Not_found ->
    let ext = find_ext j.job_ext in
    log 0 "Error for job from %s, looking for %d, called by %a" ext.name j.job_n Expr.debug_term x;
    log 0 "watched : %a" (Util.pp_list ~sep:" || " Expr.debug_term) j.watched;
    log 0 "not_watched : %a" (Util.pp_list ~sep:" || " Expr.debug_term) j.not_watched;
    assert false

let new_job id k watched not_watched f = {
  job_ext = id;
  job_n = k;
  watched = watched;
  not_watched = not_watched;
  job_callback = f;
  job_done = - 1;
}

let watch tag k args f =
  assert (k > 0);
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      let j = new_job tag k not_assigned (List.rev_append l assigned) f in
      List.iter (add_job j) not_assigned
    | [] (* i > 0 *) ->
      let l = List.rev_append not_assigned assigned in
      let to_watch, not_watched = Util.list_split_at k l in
      let j = new_job tag k to_watch not_watched f in
      List.iter (add_job j) to_watch;
      call_job j
    | y :: r ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  let t' = Builtin.tuple args in
  let l = try H.find watchers t' with Not_found -> [] in
  if not (List.mem tag l) then begin
    log 10 "New watch from %s, %d among : %a" (find_ext tag).name k (Util.pp_list ~sep:" || " Expr.debug_term) args;
    H.add watchers t' (tag :: l);
    split [] [] k (List.sort_uniq Expr.Term.compare args)
  end

(*
let rec try_eval t =
  assert (not (is_assigned t));
  log 7 "Try-Eval of %a" Expr.debug_term t;
  match Expr.(t.term) with
  | Expr.App (f, _, l) ->
    begin try
        begin match Expr.eval t with
          | Expr.Interpreted (v, lvl) ->
            set_assign t v lvl;
            Some v
          | Expr.Waiting t' ->
            begin match try_eval t' with
              | None -> add_wait_eval t t'; None
              | Some _ -> try_eval t
            end
        end
      with
      | Expr.Cannot_interpret _ -> None
    end
  | _ ->
    begin try
        Some (fst (get_assign t))
      with Not_assigned _ ->
        None
    end
*)

let rec assign_watch t = function
  | [] -> ()
  | j :: r ->
    begin
      try
        update_watch t j
      with Absurd _ as e ->
        List.iter (fun job -> add_job job t) r;
        raise e
    end;
    assign_watch t r

and set_assign t v lvl =
  try
    let v', lvl' = M.find eval_map t in
    log 5 "Assigned (%d) : %a -> %a / %a" lvl' Expr.debug_term t Expr.debug_term v' Expr.debug_term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments"
  with Not_found ->
    log 5 "Assign (%d) : %a -> %a" lvl Expr.debug_term t Expr.debug_term v;
    M.add eval_map t (v, lvl);
    let l = try hpop watch_map t with Not_found -> [] in
    log 10 " Found %d watchers" (List.length l);
    assign_watch t l
    (*
    begin try
        let l = pop wait_eval t in
        log 10 " Waiting for %a :" Expr.debug_term t;
        List.iter (fun t' -> log 10 "  -> %a" Expr.debug_term t') l;
        List.iter (fun t' -> ignore (try_eval t')) l
      with Not_found -> () end
      *)

let model () = M.fold eval_map (fun t (v, _) acc -> (t, v) :: acc) []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let assume s =
  log 5 "New slice of length %d" s.length;
  try
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit f, lvl ->
        log 1 " Assuming (%d) %a" lvl Expr.debug_formula f;
        ext_iter (fun ext -> ext.assume (f, lvl))
      | Assign (t, v), lvl -> set_assign t v lvl
    done;
    log 8 "Propagating (%d)" (Stack.length propagate_stack);
    do_propagate s.propagate;
    do_push s.push;
    Sat
  with Absurd (l, p) ->
    log 3 "Conflict '%s'" p.proof_name;
    List.iter (fun f -> log 1 " |- %a" Expr.debug_formula f) l;
    Unsat (l, p)

let if_sat s =
  log 5 "Iteration with complete model";
  begin try
      ext_iter (fun ext -> ext.if_sat ())
    with Absurd _ -> assert false
  end;
  do_push s.push

let assign t =
  log 5 "Finding assignment for %a" Expr.debug_term t;
  try
    let res = Expr.assign t in
    log 5 " -> %a" Expr.debug_term res;
    res
  with Expr.Cannot_assign _ ->
    _fail (Util.sprintf
             "Expected to be able to assign symbol %a\nYou may have forgotten to activate an extension" Expr.debug_term t)

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if not (Expr.is_interpreted p) then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e =
  preprocess e;
  match Expr.(e.formula) with
  | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
  | Expr.Pred p -> iter_assign_aux f p
  | _ -> ()

exception Found_eval of bool * int
let eval_aux f =
  try
    ext_iter (fun ext ->
        match ext.eval_pred f with
        | Some (b, lvl) -> raise (Found_eval (b, lvl))
        | _ -> ());
    Unknown
  with Found_eval (b, lvl) ->
    Valued (b, lvl)

let eval formula =
  log 5 "Evaluating formula : %a" Expr.debug_formula formula;
  eval_aux formula


