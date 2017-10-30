
let section = Section.make ~parent:Proof.section "logic"

(* Proof steps *)
(* ************************************************************************ *)

let intro =
  let compute ctx =
    match Term.uncurry_app @@ Proof.goal ctx with
    | { Term.term = Term.Id f }, [p; q] ->
      let env' = Proof.Env.intro (Proof.env ctx) p in
      let goal' = q in
      Proof.Env.find env' p, Proof.mk_ctx env' goal'
    | _ ->
      raise (Proof.Failure ("Can't introduce formula", ctx))
  in
  let elaborate id = function
    | [| body |] -> Term.lambda id body
    | _ -> assert false
  in
  let coq = Proof.Last_but_not_least,
            (fun fmt p ->
               Format.fprintf fmt "intro %a."


