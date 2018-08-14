
let section = Section.make ~parent:Proof.section "quant"

let tag ?dk ?coq id =
  CCOpt.iter (fun s -> Expr.Id.tag id Dedukti.Print.name @@ Pretty.Exact s) dk;
  CCOpt.iter (fun s -> Expr.Id.tag id Coq.Print.name @@ Pretty.Exact s) coq;
  ()

(* Epsilon prelude *)
(* ************************************************************************ *)

let epsilon_prelude_id = Expr.Id.mk_new "epsilon" ()
let epsilon_prelude = Proof.Prelude.require epsilon_prelude_id

let () = tag epsilon_prelude_id ~dk:"epsilon" ~coq:"Coq.Logic.Epsilon"

(* Useful constants for instanciation *)
(* ************************************************************************ *)

let not_ex_all_not =
  let u = Term.var "U" Term._Type in
  let () = Term.coq_inferred u in
  let u_t = Term.id u in
  let u_to_prop = Term.arrow u_t Term._Prop in
  let p = Term.var "P" u_to_prop in
  let () = Term.coq_inferred p in
  let p_t = Term.id p in
  let n = Term.var "n" u_t in
  let n_t = Term.id n in
  let n' = Term.var "n" u_t in
  let n_t' = Term.id n' in
  Term.declare "not_ex_all_not" @@
  Term.foralls [u; p] @@
  Term.arrow
    (Term.app Term.not_term @@ Term.exist n (Term.app p_t n_t))
    (Term.forall n' @@ Term.app Term.not_term (Term.app p_t n_t'))

let not_ex_not_all =
  let u = Term.var "U" Term._Type in
  let () = Term.coq_inferred u in
  let u_t = Term.id u in
  let u_to_prop = Term.arrow u_t Term._Prop in
  let p = Term.var "P" u_to_prop in
  let () = Term.coq_inferred p in
  let p_t = Term.id p in
  let n = Term.var "n" u_t in
  let n_t = Term.id n in
  let n' = Term.var "n" u_t in
  let n_t' = Term.id n' in
  Term.declare "not_ex_not_all" @@
  Term.foralls [u; p] @@
  Term.arrow
    (Term.app Term.not_term @@ Term.exist n (
        Term.app Term.not_term @@ Term.app p_t n_t))
    (Term.forall n' @@ (Term.app p_t n_t'))

let not_ex_all_not_term = Term.id not_ex_all_not
let not_ex_not_all_term = Term.id not_ex_not_all

let () =
  tag not_ex_all_not  ~dk:"classical.not_ex_all_not"  ~coq:"not_ex_all_not";
  tag not_ex_not_all  ~dk:"classical.not_ex_not_all"  ~coq:"not_ex_not_all";
  ()

(* Quantified formula matching *)
(* ************************************************************************ *)

let match_all =
  let a = Term.var "a" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let body = Term.var "p" Term._Prop in
  let body_t = Term.id body in
  let pat = Term.forall x body_t in
  (fun t ->
     try
       let s = Term.pmatch ~pat t in
       let var =
         match Term.S.Id.get x s with
         | { Term.term = Term.Id v } -> v
         | _ -> assert false
       in
       let res = Term.S.Id.get body s in
       Some(var, res)
     with
     | Term.Match_Impossible _ -> None
     | Not_found ->
       Util.error ~section "Absent binding after pattern matching";
       assert false)

let match_ex =
  let a = Term.var "a" Term._Type in
  let a_t = Term.id a in
  let x = Term.var "x" a_t in
  let body = Term.var "p" Term._Prop in
  let body_t = Term.id body in
  let pat = Term.exist x body_t in
  (fun t ->
     try
       let s = Term.pmatch ~pat t in
       let var =
         match Term.S.Id.get x s with
         | { Term.term = Term.Id v } -> v
         | _ -> assert false
       in
       let res = Term.S.Id.get body s in
       Some(var, res)
     with
     | Term.Match_Impossible _ -> None
     | Not_found ->
       Util.error ~section "Absent binding after pattern matching";
       assert false)

let match_not_ex t =
  CCOpt.(Logic.match_not t >>= match_ex)

let match_not_all t =
  CCOpt.(Logic.match_not t >>= match_all)

(* Instanciation *)
(* ************************************************************************ *)

let rec inst_not_ex f = function
  | [] -> f
  | x :: r ->
    begin match match_not_ex @@ Term.ty f with
      | Some (var, body) ->
        let u = var.Expr.id_type in
        let t =
          match Logic.match_not body with
          | None ->
            let p = Term.lambda var body in
            Term.apply not_ex_all_not_term [u; p; f; x]
          | Some body' ->
            let p = Term.lambda var body' in
            Term.apply not_ex_not_all_term [u; p; f; x]
        in
        inst_not_ex t r
      | None ->
        Util.debug ~section "@[<hv>Expected a negated existencial:@ @[<hv>%a :@ %a@]@]"
          Term.print f Term.print (Term.ty f);
        raise (Invalid_argument "Quant.inst_not_ex")
    end

(* Useful constants for epsilons *)
(* ************************************************************************ *)

let inhabited =
  let a = Term.var "A" Term._Type in
  Term.declare "inhabited" @@
  Term.forall a Term._Prop

let inhabited_term = Term.id inhabited

let inhabits =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  Term.declare "inhabits" @@
  Term.forall a @@
  Term.arrow a_t @@
  Term.app inhabited_term a_t

let inhabits_term = Term.id inhabits

let epsilon =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  Term.declare "epsilon" @@
  Term.forall a @@
  Term.arrows [
    Term.app inhabited_term a_t;
    Term.arrow a_t Term._Prop;
  ] a_t

let epsilon_term = Term.id epsilon

let epsilon_spec =
  let a = Term.var "A" Term._Type in
  let () = Term.coq_implicit a in
  let a_t = Term.id a in
  let i = Term.var "i" (Term.app inhabited_term a_t) in
  let i_t = Term.id i in
  let p = Term.var "P" (Term.arrow a_t Term._Prop) in
  let p_t = Term.id p in
  let x = Term.var "x" a_t in
  let x_t = Term.id x in
  Term.declare "epsilon_spec" @@
  Term.foralls [a; i; p] @@
  Term.arrow (Term.exist x (Term.app p_t x_t)) @@
  Term.app p_t (Term.apply epsilon_term [a_t; i_t; p_t])

let epsilon_spec_term = Term.id epsilon_spec

let not_all_ex_not =
  let u = Term.var "U" Term._Type in
  let () = Term.coq_inferred u in
  let u_t = Term.id u in
  let u_to_prop = Term.arrow u_t Term._Prop in
  let p = Term.var "P" u_to_prop in
  let () = Term.coq_inferred p in
  let p_t = Term.id p in
  let n = Term.var "n" u_t in
  let n_t = Term.id n in
  let n' = Term.var "n" u_t in
  let n_t' = Term.id n' in
  Term.declare "not_all_ex_not" @@
  Term.foralls [u; p] @@
  Term.arrow
    (Term.app Term.not_term @@ Term.forall n (Term.app p_t n_t))
    (Term.exist n' @@ Term.app Term.not_term (Term.app p_t n_t'))

let not_all_not_ex =
  let u = Term.var "U" Term._Type in
  let () = Term.coq_inferred u in
  let u_t = Term.id u in
  let u_to_prop = Term.arrow u_t Term._Prop in
  let p = Term.var "P" u_to_prop in
  let () = Term.coq_inferred p in
  let p_t = Term.id p in
  let n = Term.var "n" u_t in
  let n_t = Term.id n in
  let n' = Term.var "n" u_t in
  let n_t' = Term.id n' in
  Term.declare "not_all_not_ex" @@
  Term.foralls [u; p] @@
  Term.arrow
    (Term.app Term.not_term @@ Term.forall n (
        Term.app Term.not_term @@ Term.app p_t n_t))
    (Term.exist n' @@ (Term.app p_t n_t'))

let not_all_ex_not_term = Term.id not_all_ex_not
let not_all_not_ex_term = Term.id not_all_not_ex

let () =
  tag inhabited       ~dk:"logic.inhabited"           ~coq:"inhabited";
  tag inhabits        ~dk:"logic.inhabits"            ~coq:"inhabits";
  tag epsilon         ~dk:"epsilon.epsilon"           ~coq:"epsilon";
  tag epsilon_spec    ~dk:"epsilon.epsilon_spec"      ~coq:"epsilon_spec";
  tag not_all_ex_not  ~dk:"classical.not_all_ex_not"  ~coq:"not_all_ex_not";
  tag not_all_not_ex  ~dk:"classical.not_all_not_ex"  ~coq:"not_all_not_ex";
  ()

(* Term building for espilon instanciation *)
(* ************************************************************************ *)

let rec inst_epsilon f = function
  | [] -> f
  | ((x, witness) :: r) as l ->
    begin match match_ex @@ Term.ty f with
      | Some (var, body) ->
        let a = var.Expr.id_type in
        let p = Term.lambda var body in
        let i = Term.apply inhabits_term [a; witness] in
        Util.debug ~section "inst_epsilon: @[<v>v : %a@ i : %a@ p : %a@ f : %a@]"
          Expr.Id.print var Term.print i Term.print p Term.print f;
        let t = Term.apply epsilon_spec_term [a; i; p; f] in
        inst_epsilon t r
      | None ->
        begin match match_not_all @@ Term.ty f with
          | Some (var, body) ->
            let u = var.Expr.id_type in
            let t =
              match Logic.match_not body with
              | None ->
                let p = Term.lambda var body in
                Term.apply not_all_ex_not_term [u; p; f]
              | Some body' ->
                let p = Term.lambda var body' in
                Term.apply not_all_not_ex_term [u; p; f]
            in
            inst_epsilon t l
          | None ->
            Util.error ~section
              "@[<hv 2>Expected an existencial (or not all) but got@ %a: @[<hov>%a@]"
              Term.print f Term.print (Term.ty f);
            raise (Invalid_argument "Quant.inst_epsilon")
        end
    end

