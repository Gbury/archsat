
let log = Debug.log

(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)

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
  eval_map : (term * int) M.t;
  wait_eval : term list M.t;
  watch_map : ((term * term) -> unit) list M.t;
  ext_levels : int Vector.t;
}

type res =
  | Sat of level
  | Unsat of formula list * proof

type eval_res =
  | Valued of bool * int
  | Unknown

(* Extensions registering *)
(* ************************************************************************ *)

exception Absurd of formula list
exception Extension_not_found of string

type term_eval =
  | Interpreted of term * int
  | Waiting of term

type extension = {
  name : string;
  assume : slice -> unit;
  assign : term -> term option;
  eval_term : term -> term_eval;
  eval_pred : term -> (bool * int) option;
  interprets : Expr.ty Expr.function_descr Expr.var -> bool;
  backtrack : int -> unit;
  current_level : unit -> int;
}

let dummy_ext = {
  name = "";
  assume = (fun _ -> assert false);
  assign = (fun _ -> assert false);
  eval_term = (fun _ -> assert false);
  eval_pred = (fun _ -> assert false);
  interprets = (fun _ -> assert false);
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
    assert (not (Vector.exists aux active));
    Vector.push active r
  with Not_found ->
    raise (Extension_not_found ext)

let list_extensions () = List.map (fun r -> r.name) !extensions

(* Acces functions for active extensions *)
let n_ext () = Vector.size active

let ext_get i = Vector.get active i

let is_interpreted f = Vector.exists (fun r -> r.interprets f) active

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* Internal exceptions (not exported) *)
exception Wait_eval of term
exception Found_eval of term

(* Exported exceptions *)
exception Not_assigned of term

(* Convenience function *)
let pop key map_ref =
  let res = M.find key !map_ref in
  map_ref := M.remove key !map_ref;
  res

(* The current assignment map, term -> value *)
let eval_map = ref M.empty
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = ref M.empty
(* Map of terms watched by extensions, term -> continuation list *)
let watch_map = ref M.empty

let is_assigned t =
  try ignore (M.find t !eval_map); true with Not_found -> false

let get_assign t =
  try M.find t !eval_map with Not_found -> raise (Not_assigned t)

let pop_wait_eval t = pop t wait_eval

let pop_watch t = pop t watch_map

let add_wait_eval t t' =
  assert (not (is_assigned t));
  let l = try M.find t' !wait_eval with Not_found -> [] in
  wait_eval := M.add t' (List.sort_uniq Expr.Term.compare (t :: l)) !wait_eval

let add_watch t f =
  let l = try M.find t !watch_map with Not_found -> [] in
  watch_map := M.add t (f :: l) !watch_map

let rec try_eval t =
  assert (not (is_assigned t));
  log 7 "Try-Eval of %a" Expr.debug_term t;
  match Expr.(t.term) with
  | Expr.App (f, _, l) ->
    begin try
        for i = 0 to n_ext () do
          if (ext_get i).interprets f then
            begin match (ext_get i).eval_term t with
              | Interpreted (v, lvl) ->
                set_assign t v lvl;
                raise (Found_eval v)
              | Waiting t' ->
                raise (Wait_eval t')
            end
        done;
        None
      with
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
  eval_map := M.add t (v, lvl) !eval_map;
  begin try
      let l = pop_watch t in
      log 10 "Found %d watchers" (List.length l);
      List.iter (fun f -> f (t, v)) l
    with Not_found -> () end;
  begin try
      let l = pop_wait_eval t in
      log 10 "Waiting for %a :" Expr.debug_term t;
      List.iter (fun t' -> log 10 " -> %a" Expr.debug_term t') l;
      List.iter (fun t' -> ignore (try_eval t')) l
    with Not_found -> () end

let watch t f =
  match try_eval t with
  | None -> add_watch t f
  | Some v -> f (t, v)

let model () = M.fold (fun t (v, _) acc -> (t, v) :: acc) !eval_map []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let dummy = {
  eval_map = M.empty;
  wait_eval = M.empty;
  watch_map = M.empty;
  ext_levels = Vector.make_empty ~-1;
}

let current_level () = {
  eval_map = !eval_map;
  wait_eval = !wait_eval;
  watch_map = !watch_map;
  ext_levels = Vector.init (Vector.size active)
      (fun i -> (ext_get i).current_level ()) ~-1;
}

let backtrack s =
  log 3 "Backtracking";
  eval_map := s.eval_map;
  wait_eval := s.wait_eval;
  watch_map := s.watch_map

let assume s =
  log 5 "New slice of length %d" s.length;
  for i = s.start to s.start + s.length - 1 do
    match s.get i with
    | Lit _, _ -> ()
    | Assign (t, v), lvl -> set_assign t v lvl
  done;
  let i = ref 0 in
  try
    while !i < Vector.size active do
        (ext_get !i).assume s;
        incr i
    done;
    Sat (current_level ())
  with Absurd l ->
    Unsat (l, !i)

let assign t =
  log 5 "Finding assignment for %a" Expr.debug_term t;
  let res = ref None in
  begin try
      for i = 0 to n_ext () - 1 do
        match (ext_get i).assign t with
        | None -> ()
        | Some v -> res := Some v; raise Exit
      done;
    with Exit ->
      ()
  end;
  match !res with
  | None -> assert false
  | Some v -> v

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if not (is_interpreted p) then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e = match Expr.(e.formula) with
  | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
  | Expr.Pred p -> iter_assign_aux f p
  | _ -> ()

let rec eval f =
  log 5 "Evaluating formula : %a" Expr.debug_formula f;
  match Expr.(f.formula) with
  | Expr.Equal (a, b) ->
    begin try
        let a', lvl_a = get_assign a in
        let b', lvl_b = get_assign b in
        Valued (Expr.Term.equal a' b', max lvl_a lvl_b)
      with Not_assigned _ ->
        Unknown
    end
  | Expr.Pred p ->
    let res = ref Unknown in
    begin try
        for i = 0 to n_ext () - 1 do
          match (ext_get i).eval_pred p with
          | Some (b, lvl) -> res := Valued (b, lvl); raise Exit
          | _ -> ()
        done;
        raise Exit
      with Exit ->
        !res
    end
  | Expr.Not f' -> begin match eval f' with
      | Valued (b, lvl) -> Valued (not b, lvl)
      | Unknown -> Unknown
    end
  | _ -> Unknown



