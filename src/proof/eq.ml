(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Proof.section "eq"

let tag ?dk ?coq id =
  CCOpt.iter (fun s -> Expr.Id.tag id Dedukti.Print.name @@ Pretty.Exact s) dk;
  CCOpt.iter (fun s -> Expr.Id.tag id Coq.Print.name @@ Pretty.Exact s) coq;
  ()

(* Useful constants *)
(* ************************************************************************ *)

let eq_ind =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let a_to_prop = Term.arrow a_t Term._Prop in
  let x = Term.var "x" a_t in
  let x_t = Term.id x in
  let p = Term.var "P" a_to_prop in
  let p_t = Term.id p in
  let y = Term.var "y" a_t in
  let y_t = Term.id y in
  let p_x = Term.app p_t x_t in
  let eq = Term.apply Term.equal_term [a_t; x_t; y_t] in
  Term.declare "eq_ind" @@
  Term.foralls [a; x; p] @@
  Term.arrow p_x @@
  Term.forall y @@
  Term.arrow eq @@
  (Term.app p_t y_t)

let eq_subst, eq_subst_alias =
  let a = Term.var "A" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let x_t = Term.id x in
  let a_to_prop = Term.arrow a_t Term._Prop in
  let p = Term.var "P" a_to_prop in
  let p_t = Term.id p in
  let y = Term.var "y" a_t in
  let y_t = Term.id y in
  let p_x = Term.app p_t x_t in
  let proof = Term.var "proof" p_x in
  let eq = Term.apply Term.equal_term [a_t; x_t; y_t] in
  let e = Term.var "e" eq in
  let t = Term.lambdas [a; x; y; p; e; proof] (
      Term.(apply (id eq_ind) [a_t; x_t; p_t; id proof; y_t; id e])
    ) in
  let id = Term.declare "eq_subst" (Term.ty t) in
  id, Proof.Prelude.alias id (function
      | Proof.Coq -> Some t | Proof.Dot | Proof.Dedukti -> None)

let eq_refl =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let x_t = Term.id x in
  Term.declare "eq_refl" @@
  Term.foralls [a; x] @@
  Term.apply Term.equal_term [a_t; x_t; x_t]

let eq_sym =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let () = Term.coq_implicit x in
  let () = Term.coq_implicit y in
  let x_t = Term.id x in
  let y_t = Term.id y in
  Term.declare "eq_sym" @@
  Term.foralls [a; x; y] @@
  Term.arrow
    (Term.apply Term.equal_term [a_t; x_t; y_t])
    (Term.apply Term.equal_term [a_t; y_t; x_t])

let not_eq_sym =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let () = Term.coq_implicit x in
  let () = Term.coq_implicit y in
  let x_t = Term.id x in
  let y_t = Term.id y in
  Term.declare "not_eq_sym" @@
  Term.foralls [a; x; y] @@
  Term.arrow
    (Term.app Term.not_term @@ Term.apply Term.equal_term [a_t; x_t; y_t])
    (Term.app Term.not_term @@ Term.apply Term.equal_term [a_t; y_t; x_t])

let eq_trans =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let z = Term.var "z" a_t in
  let () = Term.coq_implicit x in
  let () = Term.coq_implicit y in
  let () = Term.coq_implicit z in
  let x_t = Term.id x in
  let y_t = Term.id y in
  let z_t = Term.id z in
  Term.declare "eq_trans" @@
  Term.foralls [a; x; y; z] @@
  Term.arrows [
    Term.apply Term.equal_term [a_t; x_t; y_t];
    Term.apply Term.equal_term [a_t; y_t; z_t];
  ] (Term.apply Term.equal_term [a_t; x_t; z_t])

let f_equal =
  let a = Term.var "A" Term._Type in
  let b = Term.var "B" Term._Type in
  let () = Term.coq_implicit a in
  let () = Term.coq_implicit b in
  let a_t = Term.id a in
  let b_t = Term.id b in
  let a_to_b = Term.arrow a_t b_t in
  let f = Term.var "f" a_to_b in
  let f_t = Term.id f in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let () = Term.coq_implicit x in
  let () = Term.coq_implicit y in
  let x_t = Term.id x in
  let y_t = Term.id y in
  Term.declare "f_equal" @@
  Term.foralls [a; b; f; x; y] @@
  Term.arrow
    (Term.apply Term.equal_term [a_t; x_t; y_t])
    (Term.apply Term.equal_term [
        b_t;
        Term.app f_t x_t;
        Term.app f_t y_t;
      ]
    )

let f_equal2 =
  let a1 = Term.var "A1" Term._Type in
  let a2 = Term.var "A2" Term._Type in
  let b = Term.var "B" Term._Type in
  let () = Term.coq_implicit a1 in
  let () = Term.coq_implicit a2 in
  let () = Term.coq_implicit b in
  let a1_t = Term.id a1 in
  let a2_t = Term.id a2 in
  let b_t = Term.id b in
  let a_to_b = Term.arrows [a1_t; a2_t] b_t in
  let f = Term.var "f" a_to_b in
  let f_t = Term.id f in
  let x1 = Term.var "x1" a1_t in
  let y1 = Term.var "y1" a1_t in
  let x2 = Term.var "x2" a2_t in
  let y2 = Term.var "y2" a2_t in
  let () = Term.coq_implicit x1 in
  let () = Term.coq_implicit y1 in
  let () = Term.coq_implicit x2 in
  let () = Term.coq_implicit y2 in
  let x1_t = Term.id x1 in
  let y1_t = Term.id y1 in
  let x2_t = Term.id x2 in
  let y2_t = Term.id y2 in
  Term.declare "f_equal2" @@
  Term.foralls [a1; a2; b; f; x1; y1; x2; y2] @@
  Term.arrows [
    Term.apply Term.equal_term [a1_t; x1_t; y1_t];
    Term.apply Term.equal_term [a2_t; x2_t; y2_t];
  ] @@ Term.apply Term.equal_term [
    b_t;
    Term.apply f_t [x1_t; x2_t];
    Term.apply f_t [y1_t; y2_t];
  ]

let eq_sym_term = Term.id eq_sym
let eq_ind_term = Term.id eq_ind
let eq_refl_term = Term.id eq_refl
let f_equal_term = Term.id f_equal
let eq_trans_term = Term.id eq_trans
let eq_subst_term = Term.id eq_subst
let f_equal2_term = Term.id f_equal2
let not_eq_sym_term = Term.id not_eq_sym

let () =
  tag eq_ind        ?dk:None                ~coq:"eq_ind";
  tag eq_subst      ~dk:"logic.eq_subst"    ?coq:None;
  tag eq_refl       ~dk:"logic.eq_refl"     ~coq:"eq_refl";
  tag eq_sym        ~dk:"logic.eq_sym"      ~coq:"eq_sym";
  tag not_eq_sym    ~dk:"logic.not_eq_sym"  ~coq:"not_eq_sym";
  tag eq_trans      ~dk:"logic.eq_trans"    ~coq:"eq_trans";
  tag f_equal       ~dk:"logic.f_equal"     ~coq:"f_equal";
  tag f_equal2      ~dk:"logic.f_equal2"    ~coq:"f_equal2";
  ()

(* Equality coercions for env lookups *)
(* ************************************************************************ *)

let match_eq =
  let a = Term.var "a" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let x_t = Term.id x in
  let y_t = Term.id y in
  let pat = Term.apply Term.equal_term [a_t; x_t; y_t] in
  (fun t ->
     try
       let s = Term.pmatch ~pat t in
       let left = Term.S.Id.get x s in
       let right = Term.S.Id.get y s in
       Some (left, right)
     with
     | Not_found ->
       Util.error ~section "Absent binding after pattern matching";
       assert false
     | Term.Match_Impossible _ ->
       None
  )

let match_neq =
  let a = Term.var "a" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let y = Term.var "y" a_t in
  let x_t = Term.id x in
  let y_t = Term.id y in
  let pat =
    Term.app Term.not_term @@
    Term.apply Term.equal_term [a_t; x_t; y_t] in
  (fun t ->
     try
       let s = Term.pmatch ~pat t in
       let left = Term.S.Id.get x s in
       let right = Term.S.Id.get y s in
       Some (left, right)
     with
     | Not_found ->
       Util.error ~section "Absent binding after pattern matching";
       assert false
     | Term.Match_Impossible _ ->
       None
  )

let coercion_f t =
  match match_eq t with
  | Some (a, b) ->
    [ Proof.Env.(Wrapped {
          term = Term.apply Term.equal_term [Term.ty a; b; a];
          wrap = (fun e -> Term.apply eq_sym_term [Term.ty a; b; a; e]);
        } ) ]
  | None ->
    begin match match_neq t with
      | Some (a, b) ->
        [ Proof.Env.(Wrapped {
              term =
                Term.app Term.not_term @@
                Term.apply Term.equal_term [Term.ty a; b; a];
              wrap = (fun e -> Term.apply not_eq_sym_term [Term.ty a; b; a; e]);
            } ) ]
      | None -> []
    end

let () = Proof.Env.register ("eq", coercion_f)

(* Tactic for equality reflexivity *)
(* ************************************************************************ *)

let refl_match =
  let a = Term.var "a" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let x_t = Term.id x in
  let pat = Term.apply Term.equal_term [a_t; x_t; x_t] in
  (fun t ->
     try
       let s = Term.pmatch ~pat t in
       Some (Term.S.Id.get x s)
     with
     | Term.Match_Impossible _ -> None
     | Not_found ->
       Util.error ~section "Absent binding after pattern matching";
       assert false
  )

let refl pos =
  let seq = Logic.extract_open pos in
  let goal = Proof.goal seq in
  match refl_match goal with
  | None -> raise (Proof.Failure ("couldn't apply eq_refl", pos))
  | Some t -> Logic.exact [] (Term.apply eq_refl_term [Term.ty t; t]) pos

(* Tactic for equality transitivity *)
(* ************************************************************************ *)

let trans l pos =
  let rec aux_map acc = function
    | [] -> List.rev acc
    | [t] -> aux_map (t :: acc) []
    | (x, y, proof) :: (x', y', proof') :: r ->
      assert (Term.Reduced.equal y x');
      let new_proof = Term.apply eq_trans_term [Term.ty x; x; y; y'; proof; proof'] in
      aux_map ((x, y', new_proof) :: acc) r
  in
  let rec aux_fixpoint = function
    | [] -> assert false
    | [(_, _, res)] -> res
    | l -> aux_fixpoint (aux_map [] l)
  in
  let seq = Logic.extract_open pos in
  let env = Proof.env seq in
  let l' = List.map (fun (x, y) ->
      let eq = Term.apply Term.equal_term [x.Term.ty; x; y] in
      let proof = Proof.Env.find env eq in
      (x, y, proof)) l in
  Logic.exact [] (aux_fixpoint l') pos



(* Tactic for substitution *)
(* ************************************************************************ *)

let fresh =
  let r = ref 0 in
  (fun ty -> incr r; Term.var (Format.sprintf "?%d" !r) ty)

let subst ~eq ~by:u path goal pos =
  let t =
    match Position.Proof.apply path goal with
    | None -> raise (Proof.Failure ("Eq.subst", pos))
    | Some t -> t
  in
  let a = Term.ty t in
  let x = fresh a in
  let p =
    match Position.Proof.substitute path ~by:(Term.id x) goal with
    | None -> raise (Proof.Failure ("Eq.subst", pos))
    | Some t' -> Term.lambda x @@ t'
  in
  let p1, p2 = Logic.apply2 [eq_subst_alias] (Term.apply eq_subst_term [a; u; t; p]) pos in
  let () = eq p1 in
  p2

let replace ~eq ~by:u v pos =
  let goal = Proof.goal @@ Logic.extract_open pos in
  match Position.Proof.find v goal with
  | Some p -> subst ~eq ~by:u p goal pos
  | None ->
    Util.error ~section "Couldn't @[<v>find: %a@   in: %a@]"
      Term.print v Term.print goal;
    raise (Proof.Failure ("Eq.replace", pos))

(* Tactic for congruence closure *)
(* ************************************************************************ *)

let congruence_term f xys pos =
  match xys with
  | [] -> raise (Proof.Failure ("Eq.congruence", pos))
  | [x, y] ->
    begin match Proof.match_arrow @@ Term.ty f with
      | None ->
        Util.error ~section "@[<hv>Couldn't match arrow type for:@ %a : @[<hov>%a@]@]"
          Term.print f Term.print (Term.ty f);
        raise (Proof.Failure ("Eq.congruence", pos))
      | Some (a, b) ->
        assert (Term.Reduced.equal a @@ Term.ty x);
        assert (Term.Reduced.equal (Term.ty x) (Term.ty y));
        pos
        |> Logic.apply1 [] (Term.apply f_equal_term [a; b; f; x; y])
        |> Logic.ensure Logic.trivial
    end
  | [x1, y1; x2, y2] ->
    begin match Proof.match_n_arrows 2 @@ Term.ty f with
      | Some ([a1; a2], b) ->
        assert (Term.Reduced.equal a1 @@ Term.ty x1);
        assert (Term.Reduced.equal a1 @@ Term.ty y1);
        assert (Term.Reduced.equal a2 @@ Term.ty x2);
        assert (Term.Reduced.equal a2 @@ Term.ty y2);
        pos
        |> Logic.apply2 [] (Term.apply f_equal2_term [a1; a2; b; f; x1; y1; x2; y2])
        |> Logic.split
          ~left:(Logic.ensure Logic.trivial)
          ~right:(Logic.ensure Logic.trivial)
      | _ -> raise (Proof.Failure ("Eq.congruence", pos))
    end
  | l ->
    pos
    |> Logic.fold (fun (u, v) -> replace ~eq:(Logic.ensure Logic.trivial) ~by:u v) l
    |> refl

let congruence_prop f l pos =
  pos
  |> Logic.fold (fun (u, v) -> replace ~eq:(Logic.ensure Logic.trivial) ~by:v u) l
  |> Logic.ensure Logic.trivial

