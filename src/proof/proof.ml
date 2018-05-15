
let section = Section.make "proof"

(* Proof environments *)
(* ************************************************************************ *)

module Env = struct

  exception Added_twice of Term.t
  exception Not_introduced of Term.t

  let () =
    Printexc.register_printer (function
        | Added_twice f ->
          Some (Format.asprintf
                  "Following formula has been added twice to context:@ %a"
                  Term.print f)
        | Not_introduced f ->
          Some (Format.asprintf
                  "Following formula is used in a context where it is not declared:@ %a"
                  Term.print f)
        | _ -> None
      )

  module Mt = Map.Make(Term)
  module Ms = Map.Make(String)

  type t = {
    (** Map between terms and term ids *)
    names : Term.id Mt.t;
    (** Options for nice names *)
    prefix : string;  (** current prefix *)
    count : int Ms.t; (** use count for each prefix *)
  }

  let print_aux fmt (t, id) =
    Format.fprintf fmt "%a: @[<hov>%a@]" Expr.Print.id id Term.print t

  let print fmt t =
    let l = Mt.bindings t.names in
    let l = List.sort (fun (_, x) (_, y) ->
        compare x.Expr.id_name y.Expr.id_name) l in
    CCFormat.(list ~sep:(return "@ ") print_aux) fmt l

  let empty = {
    names = Mt.empty;
    prefix = "";
    count = Ms.empty;
  }

  let prefix t s =
    { t with prefix = s }

  let mem t f =
    Mt.mem f t.names

  let find t f =
    try Mt.find f t.names
    with Not_found -> raise (Not_introduced f)

  let count t s =
    try Ms.find s t.count with Not_found -> 0

  let add t id =
    let f = id.Expr.id_type in
    match Mt.find f t.names with
    | name -> raise (Added_twice f)
    | exception Not_found ->
      { t with names = Mt.add f id t.names; }

  let intro t f =
    match Mt.find f t.names with
    | name -> raise (Added_twice f)
    | exception Not_found ->
      let n = count t t.prefix in
      let name = Format.sprintf "%s%d" t.prefix n in
      let id = Term.declare name f in
      { t with
        names = Mt.add f id t.names;
        count = Ms.add t.prefix (n + 1) t.count;
      }

end

(* Proof preludes *)
(* ************************************************************************ *)

module Prelude = struct

  let section = Section.make ~parent:section "prelude"

  module Aux = struct

    type t =
      | Require of unit Expr.id
      | Alias of Term.id * Term.t

    let _discr = function
      | Require _ -> 0
      | Alias _ -> 1

    let hash_aux t id =
      CCHash.(pair int Expr.Id.hash) (_discr t, id)

    let hash t =
      match t with
      | Require id -> hash_aux t id
      | Alias (id, _) -> hash_aux t id

    let compare t t' =
      match t, t' with
      | Require v, Require v' -> Expr.Id.compare v v'
      | Alias (v, e), Alias (v', e') ->
        let res = Expr.Id.compare v v' in
        if res = 0 then assert (Term.equal e e');
        res
      | _ -> Pervasives.compare (_discr t) (_discr t')

    let equal t t' = compare t t' = 0

    let print fmt = function
      | Require id ->
        Format.fprintf fmt "require: %a" Expr.Id.print id
      | Alias (v, t) ->
        Format.fprintf fmt "alias: %a ->@ %a" Expr.Print.id v Term.print t

  end

  include Aux

  module S = Set.Make(Aux)
  module G = Graph.Imperative.Digraph.Concrete(Aux)
  module T = Graph.Topological.Make_stable(G)
  module O = Graph.Oper.I(G)

  let dep_graph = G.create ()

  let mk ~deps t =
    let () = G.add_vertex dep_graph t in
    let () = List.iter (fun x ->
        Util.debug ~section "%a ---> %a" print x print t;
        G.add_edge dep_graph x t) deps in
    t

  let require ?(deps=[]) s = mk ~deps (Require s)
  let alias ?(deps=[]) id t = mk ~deps (Alias (id, t))

  let topo l iter =
    let s = List.fold_left (fun s x -> S.add x s) S.empty l in
    let _ = O.add_transitive_closure ~reflexive:true dep_graph in
    T.iter (fun v -> if S.exists (G.mem_edge dep_graph v) s then iter v) dep_graph

end

(* Proof printing data *)
(* ************************************************************************ *)

type lang =
  | Coq     (**)
(* Proof languages supported. *)

type pretty =
  | Branching           (* All branches are equivalent *)
  | Last_but_not_least  (* Last branch is the 'rest of the proof *)
(** Pretty pinting information to know better how to print proofs.
    For instance, 'split's would probably be [Branching], while
    cut/pose proof, would preferably be [Last_but_not_least]. *)

(* Proofs *)
(* ************************************************************************ *)

type sequent = {
  env : Env.t;
  goal : Term.t;
}

type ('input, 'state) step = {

  (* Printing information *)
  print : lang ->
    pretty * (Format.formatter -> 'state -> unit);

  (* Semantics *)
  compute   : sequent -> 'input -> 'state * sequent array;
  prelude   : 'state -> Prelude.t list;
  elaborate : 'state -> Term.t array -> Term.t;
}


type node = {
  pos : pos;
  proof : proof_node;
}

and pos = node array * int

and proof_node =
  | Open  : sequent -> proof_node
  | Proof : (_, 'state) step * 'state * node array -> proof_node

(* Alias for proof *)
type proof = node array
(** Simpler option would be a node ref, but it would complexify functions
    and positions neddlessly. *)


(* Proof tactics *)
type ('a, 'b) tactic = 'a -> 'b
(** The type of tactics. Should represent computations that manipulate
    proof positions. Using input ['a] and output ['b].

    Most proof tactics should take a [pos] as input, and return:
    - [unit] if it closes the branch
    - a single [pos] it it does not create multple branches
    - a tuple, list or array of [pos] if it branches
*)


(* Sequents *)
(* ************************************************************************ *)

let env { env; _ } = env
let goal { goal; _ } = goal
let mk_sequent env goal = Env.{ env; goal; }

let print_sequent fmt sequent =
  Format.fprintf fmt
    "@[<hv 2>sequent:@ @[<hv 2>env:@ @[<v>%a@]@] @[<hv 2>goal:@ @[<hov>%a@]@]@]"
    Env.print sequent.env Term.print sequent.goal

(* Failure *)
(* ************************************************************************ *)

exception Failure of string * sequent

let () = Printexc.register_printer (function
    | Failure (msg, sequent) ->
      Some (Format.asprintf "@[<hv>In context:@ %a@ %s@]" print_sequent sequent msg)
    | _ -> None)

(* Steps *)
(* ************************************************************************ *)

let _prelude _ = []

let mk_step ?(prelude=_prelude) ~coq ~compute ~elaborate = {
  prelude; compute; elaborate;
  print = (function Coq -> coq);
}

(* Building proofs *)
(* ************************************************************************ *)

let get ((t, i) : pos) = t.(i)
let set ((t, i) as pos : pos) step state branches =
  match (get pos).proof with
  | Open _ ->
    t.(i) <- { pos; proof = Proof (step, state, branches); }
  | Proof _ ->
    Util.error ~section "Trying to apply reasonning step to an aleardy closed proof";
    assert false

let dummy_node = {
  pos = [| |], -1;
  proof = Open (mk_sequent Env.empty Term.true_term);
}

let mk_branches n f =
  let res = Array.make n dummy_node in
  for i = 0 to n - 1 do
    let pos = (res, i) in
    res.(i) <- { pos; proof = f i; }
  done;
  res

let mk sequent = mk_branches 1 (fun _ -> Open sequent)

let apply_step pos step input =
  match (get pos).proof with
  | Proof _ ->
    Util.error ~section "Trying to apply reasonning step to an aleardy closed proof";
    assert false
  | Open sequent ->
    let state, a = step.compute sequent input in
    let branches = mk_branches (Array.length a) (fun i -> Open a.(i)) in
    let () = set pos step state branches in
    state, Array.map (fun { pos; _} -> pos) branches

(* Printing proofs *)
(* ************************************************************************ *)

exception Open_proof

let bullet_list = [ '-'; '+' ]
let bullet_n = List.length bullet_list

let bullet depth =
  let k = depth mod bullet_n in
  let n = depth / bullet_n + 1 in
  let c = List.nth bullet_list k in
  String.make n c

let rec print_branching_coq ~depth fmt t =
  Format.fprintf fmt "%s @[<hov>%a@]"
    (bullet depth) (print_node ~depth:(depth + 1) ~lang:Coq) t

and print_bracketed_coq ~depth fmt t =
  Format.fprintf fmt "{ @[<hov>%a@] }" (print_node ~depth ~lang:Coq) t

and print_lbnl_coq ~depth fmt t =
  print_node ~depth ~lang:Coq fmt t

and print_array_coq ~depth ~pretty fmt a =
  match a with
  | [| |] -> ()
  | [| x |] -> print_node ~depth ~lang:Coq fmt x
  | _ ->
    begin match pretty with
      | Branching ->
        Format.fprintf fmt "@[<v>%a@]"
          CCFormat.(array ~sep:(return "@ ") (print_branching_coq ~depth)) a
      | Last_but_not_least ->
        let a' = Array.sub a 0 (Array.length a - 1) in
        Format.fprintf fmt "@[<v>%a@ @]"
          CCFormat.(array ~sep:(return "@ ") (print_bracketed_coq ~depth)) a';
        (* separate call to ensure tail call, useful for long proofs *)
        print_lbnl_coq ~depth fmt a.(Array.length a - 1)
    end

and print_array ~depth ~lang ~pretty fmt a =
  match lang with
  | Coq -> print_array_coq ~depth ~pretty fmt a

and print_proof_node ~depth ~lang fmt = function
  | Open _ -> raise Open_proof
  | Proof (step, state, branches) ->
    let pretty, pp = step.print lang in
    Format.fprintf fmt "@[<hov 2>%a@]" pp state;
    print_array ~depth ~lang ~pretty fmt branches

and print_node ~depth ~lang fmt { proof; _ } =
  print_proof_node ~depth ~lang fmt proof

let print ~lang fmt = function
  | [| p |] -> print_node ~lang ~depth:0 fmt p
  | _ -> assert false

(* Inspecting proofs *)
(* ************************************************************************ *)

let root = function
  | [| p |] -> p
  | _ -> assert false

let pos { pos; _ } = pos

let extract { proof; _ } = proof

let branches node =
  match node.proof with
  | Open _ -> raise Open_proof
  | Proof (_, _, branches) -> branches

(* Proof elaboration *)
(* ************************************************************************ *)

let rec elaborate_array_aux k a res i =
  if i >= Array.length a then k res
  else
    elaborate_node (fun x ->
        res.(i) <- x;
        elaborate_array_aux k a res (i + 1)) a.(i)

and elaborate_array k a =
  let res = Array.make (Array.length a) Term._Type in
  elaborate_array_aux k a res 0

and elaborate_proof_node k = function
  | Open _ -> raise Open_proof
  | Proof (step, state, branches) ->
    elaborate_array (fun args -> k @@ step.elaborate state args) branches

and elaborate_node k { proof; _ } =
  elaborate_proof_node k proof

let elaborate = function
  | [| p |] -> elaborate_node (fun x -> x) p
  | _ -> assert false

(* Match an arrow type *)
(* ************************************************************************ *)

let match_arrow ty =
  match Term.reduce ty with
  | { Term.term = Term.Binder (Term.Forall, v, ret) }
    when not (Term.occurs v ret) ->
    Some (v.Expr.id_type, ret)
  | _ -> None

let match_arrows ty =
  let rec aux acc t =
    match match_arrow t with
    | Some (arg, ret) -> aux (arg :: acc) ret
    | None -> List.rev acc, t
  in
  aux [] ty

let rec match_n_arrow acc n ty =
  if n <= 0 then Some (List.rev acc, ty)
  else begin
    match match_arrow ty with
    | None -> None
    | Some (arg_ty, ret) -> match_n_arrow (arg_ty :: acc) (n - 1) ret
  end

(* Proof steps *)
(* ************************************************************************ *)

let apply =
  let prelude (_, _, l) = l in
  let compute ctx (f, n, prelude) =
    let g = goal ctx in
    match match_n_arrow [] n f.Term.ty with
    | None ->
      Util.warn ~section
        "@[<hv 2>Expected a non-dependant product type but got:@ %a@]"
        Term.print f.Term.ty;
      assert false
    | Some (l, ret) ->
      assert (Term.equal ret g);
      let e = env ctx in
      (f, n, prelude), Array.map (fun g' -> mk_sequent e g') (Array.of_list l)
  in
  let elaborate (f, _, _) args = Term.apply f (Array.to_list args) in
  let coq = Branching, (fun fmt (f, n, _) ->
      Format.fprintf fmt "%s %a."
        (if n = 0 then "exact" else "apply") Coq.Print.term f
    ) in
  mk_step ~prelude ~coq ~compute ~elaborate

let intro =
  let prelude _ = [] in
  let compute ctx prefix =
    match Term.reduce @@ goal ctx with
    | { Term.term = Term.Binder (Term.Forall, v (* : p *), q) } ->
      if Term.occurs v q then begin
        v, [| mk_sequent (env ctx) q |]
      end else begin
        let p = v.Expr.id_type in
        let e = Env.intro (Env.prefix (env ctx) prefix) p in
        Env.find e p, [| mk_sequent e q |]
      end
    | t ->
      Util.warn ~section "Expected a universal quantification, but got: %a"
        Term.print t;
      raise (Failure ("Can't introduce formula", ctx))
  in
  let elaborate id = function
    | [| body |] -> Term.lambda id body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt p ->
      Format.fprintf fmt "intro %a." Coq.Print.id p)
  in
  mk_step ~prelude ~coq ~compute ~elaborate

let letin =
  let prelude _ = [] in
  let compute ctx (prefix, t) =
    let e = Env.prefix (env ctx) prefix in
    let e' = Env.intro e t.Term.ty in
    (Env.find e' t, t), [| mk_sequent e' (goal ctx) |]
  in
  let elaborate (id, t) = function
    | [| body |] -> Term.letin id t body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt (id, t) ->
      Format.fprintf fmt "@[<hv 2>pose proof (@,%a@;<0,-2>) as %a.@]"
        Coq.Print.term t Coq.Print.id id
    ) in
  mk_step ~prelude ~coq ~compute ~elaborate

let cut =
  let prelude _ = [] in
  let compute ctx (prefix, t) =
    let e = env ctx in
    let e' = Env.prefix e prefix in
    let e'' = Env.intro e' t in
    Env.find e'' t, [| mk_sequent e t ; mk_sequent e'' (goal ctx) |]
  in
  let elaborate id = function
    | [| t; body |] -> Term.letin id t body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt id ->
      Format.fprintf fmt "assert (%a:@ @[<hov>%a@])."
        Coq.Print.id id Coq.Print.term id.Expr.id_type
    ) in
  mk_step ~prelude ~coq ~compute ~elaborate

