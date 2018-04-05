
let section = Section.make ~parent:Proof.section "logic"

(* Logic preludes *)
(* ************************************************************************ *)

let prelude_tag = Tag.create ()

(* TODO: dispatch system for language-specific printing *)
let classical =
  Proof.Prelude.require (Expr.Id.mk_new "classical" ())
    (* -> Coq.Logic.Classical *)

(* Proof steps *)
(* ************************************************************************ *)

let nnpp_id =
  let p = Term.declare "P" Term._Prop in
  let p_t = Term.const p in
  let nnp = Term.app Term.not_term (Term.app Term.not_term p_t) in
  Term.declare "NNPP" (Term.pi p (Term.arrow nnp p_t))

let apply =
  let prelude s =
    CCOpt.get_or ~default:[] (Expr.Id.get_tag s prelude_tag)
  in
  let compute ctx f =
    let goal = Proof.goal ctx in
    let new_goal = Term.(app (const f) goal) in
    let env = Proof.Env.prefix (Proof.env ctx) prefix in
    (), [| Proof.mk_sequent env g |]
  in
  let elaborate id = function
    | [| proof |] -> assert false
    | _ -> assert false
  in
  let coq = Proof.Last_but_not_least,
            (fun fmt p ->
               Format.fprintf fmt "apply NNPP.")
  in
  Proof.mk_step ~prelude ~coq ~compute ~elaborate


let intro =
  let prelude _ = [] in
  let compute ctx prefix =
    match Term.uncurry_app @@ Proof.goal ctx with
    | f, [p; q] when Term.(equal imply_term) f ->
      let env = Proof.Env.prefix (Proof.env ctx) prefix in
      let env' = Proof.Env.intro env p in
      Proof.Env.find env' p, [| Proof.mk_sequent env' q |]
    | _ ->
      raise (Proof.Failure ("Can't introduce formula", ctx))
  in
  let elaborate id = function
    | [| body |] -> Term.lambda id body
    | _ -> assert false
  in
  let coq = Proof.Last_but_not_least,
            (fun fmt p ->
               Format.fprintf fmt "intro %a." Coq.Print.id p)
  in
  Proof.mk_step ~prelude ~coq ~compute ~elaborate


