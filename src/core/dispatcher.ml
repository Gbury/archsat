
let log = Debug.log

(* Type definitions *)
(* ************************************************************************ *)

module M = Assoc.Make(Expr.Term)
module I = Assoc.Make(struct type t = int let equal i j = i=j let hash i = i land max_int end)

type term = Expr.term
type formula = Expr.formula
type proof = int

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

type level = {
  eval_map : M.level;
  wait_eval : M.level;
  watch_map : M.level;
  job_map : I.level;
  ext_levels : int Vector.t;
}

type res =
  | Sat
  | Unsat of formula list * proof

type eval_res =
  | Valued of bool * int
  | Unknown

(* Extensions registering *)
(* ************************************************************************ *)

exception Absurd of formula list
exception Extension_not_found of string

type extension = {
  name : string;
  assume : formula * int -> unit;
  eval_pred : formula -> (bool * int) option;
  backtrack : int -> unit;
  current_level : unit -> int;
}

let dummy_ext = {
  name = "";
  assume = (fun _ -> assert false);
  eval_pred = (fun _ -> assert false);
  backtrack = (fun _ -> assert false);
  current_level = (fun _ -> assert false);
}

let extensions = ref []

let active = Vector.make 10 dummy_ext

let register r =
  assert (not (List.exists (fun r' -> r'.name = r.name) !extensions));
  extensions := r :: !extensions

let activate ext =
  let aux r = r.name = ext in
  try
    let r = List.find aux !extensions in
    if not (Vector.exists aux active) then
      Vector.push active r
    else
      Debug.log 0 "WARNING: Extension %s already activated" r.name
  with Not_found ->
    raise (Extension_not_found ext)

let list_extensions () = List.map (fun r -> r.name) !extensions

(* Acces functions for active extensions *)
let n_ext () = Vector.size active

let ext_get i = Vector.get active i

let ext_iter f = Vector.iter f active
let ext_iteri f = Vector.iteri f active

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* Internal exceptions (not exported) *)
exception Wait_eval of term
exception Found_eval of term

(* Exported exceptions *)
exception Not_assigned of term

(* Convenience function *)
let pop assoc key =
  let res = M.find assoc key in
  M.remove assoc key;
  res

let popi assoc key =
  let res = I.find assoc key in
  I.remove assoc key;
  res

(* The current assignment map, term -> value *)
let eval_map = M.create 107
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = M.create 107
(* Map of terms watched by extensions, term -> continuation list *)
let watch_map = M.create 107
let job_map = I.create 107

let is_assigned t =
  try ignore (M.find eval_map t); true with Not_found -> false

let get_assign t =
  try M.find eval_map t with Not_found -> raise (Not_assigned t)

let add_wait_eval t t' =
  assert (not (is_assigned t));
  let l = try M.find wait_eval t' with Not_found -> [] in
  M.add wait_eval t' (List.sort_uniq Expr.Term.compare (t :: l))

let add_job job_id t =
  let l = try M.find watch_map t with Not_found -> [] in
  M.add watch_map t (List.sort_uniq compare (job_id :: l))

let set_job id job = I.add job_map id job

let update_watch x job_id =
  try
    let k, args, f = popi job_map job_id in
    let rec find not_assigned acc = function
      | [] -> f ()
      | y :: r when not (is_assigned y) ->
        let l = List.rev_append (y :: not_assigned) (x :: r) in
        set_job job_id (k, l, f)
      | y :: r -> find not_assigned (y :: acc) r
    in
    let rec split i acc = function
      | [] -> find acc [] []
      | l when i <= 0 -> find acc [] l
      | y :: r when Expr.Term.equal x y -> split (i - 1) acc r
      | y :: r -> split (i - 1) (y :: acc) r
    in
    split k [] args
  with Not_found ->
    ()

let rec try_eval t =
  assert (not (is_assigned t));
  log 7 "Try-Eval of %a" Expr.debug_term t;
  match Expr.(t.term) with
  | Expr.App (f, _, l) ->
    begin try
        begin match Expr.eval t with
              | Expr.Interpreted (v, lvl) ->
                set_assign t v lvl;
                raise (Found_eval v)
              | Expr.Waiting t' ->
                raise (Wait_eval t')
        end;
        None
      with
      | Expr.Cannot_interpret _ -> None
      | Found_eval v -> Some v
      | Wait_eval t' -> begin match try_eval t' with
          | None -> add_wait_eval t t'; None
          | Some _ -> try_eval t
        end
    end
  | _ ->
    begin try
        Some (fst (get_assign t))
      with Not_assigned _ ->
        None
    end

and set_assign t v lvl =
  log 5 "Assign (%d) : %a -> %a" lvl Expr.debug_term t Expr.debug_term v;
  M.add eval_map t (v, lvl);
  begin try
      let l = pop watch_map t in
      log 10 "Found %d watchers" (List.length l);
      List.iter (update_watch t) l
    with Not_found -> () end;
  begin try
      let l = pop wait_eval t in
      log 10 "Waiting for %a :" Expr.debug_term t;
      List.iter (fun t' -> log 10 " -> %a" Expr.debug_term t') l;
      List.iter (fun t' -> ignore (try_eval t')) l
    with Not_found -> () end

let job_max = ref 0

let watch k args f =
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      incr job_max;
      List.iter (add_job !job_max) not_assigned;
      let l = List.rev_append not_assigned (List.rev_append l assigned) in
      set_job !job_max (k, l, f)
    | [] (* i > 0 *) -> f ()
    | y :: r ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  split [] [] k args

let model () = M.fold eval_map (fun t (v, _) acc -> (t, v) :: acc) []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let dummy = {
  eval_map = M.dummy_level;
  wait_eval = M.dummy_level;
  watch_map = M.dummy_level;
  job_map = I.dummy_level;
  ext_levels = Vector.make_empty ~-1;
}

let current_level () = {
  eval_map = M.current_level eval_map;
  wait_eval = M.current_level wait_eval;
  watch_map = M.current_level watch_map;
  job_map = I.current_level job_map;
  ext_levels = Vector.init (n_ext ())
      (fun i -> (ext_get i).current_level ()) ~-1;
}

let backtrack s =
  log 3 "Backtracking";
  M.backtrack eval_map s.eval_map;
  M.backtrack wait_eval s.wait_eval;
  M.backtrack watch_map s.watch_map;
  I.backtrack job_map s.job_map;
  ext_iteri (fun i ext -> ext.backtrack (Vector.get s.ext_levels i))

exception Exit_unsat of formula list * int
let assume s =
  log 5 "New slice of length %d" s.length;
  try
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit f, lvl ->
        log 8 "Assuming (%d) %a" lvl Expr.debug_formula f;
        ext_iteri (fun j ext ->
            try
              ext.assume (f, lvl)
            with Absurd l ->
              raise (Exit_unsat (l, j)))
      | Assign (t, v), lvl -> set_assign t v lvl
    done;
    Sat
  with Exit_unsat (l, j) ->
    Unsat (l, j)

let assign t =
  log 5 "Finding assignment for %a" Expr.debug_term t;
  try
      Expr.assign t
  with Expr.Cannot_assign _ ->
      assert false

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if not (Expr.is_interpreted p) then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e = match Expr.(e.formula) with
  | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
  | Expr.Pred p -> iter_assign_aux f p
  | _ -> ()

exception Found_eval of bool * int
let rec eval f =
  log 5 "Evaluating formula : %a" Expr.debug_formula f;
  try
    ext_iter (fun ext ->
        match ext.eval_pred f with
        | Some (b, lvl) -> raise (Found_eval (b, lvl))
        | _ -> ());
    Unknown
  with Found_eval (b, lvl) ->
    Valued (b, lvl)


