
module D = Dispatcher

let section = Section.make "dot"

(* Printing expressions in HTML *)
(* ************************************************************************ *)

module Print = struct

  let pos = Tag.create ()
  let name = Tag.create ()
  let assoc = Tag.create ()
  type any = Any : Term.id * 'a Expr.tag * 'a -> any

  let () =
    List.iter (function Any (id, tag, v) -> Expr.Id.tag id tag v) [
      Any (Term._Prop_id, name, "Prop");
      Any (Term.true_id,  name, "True");
      Any (Term.false_id, name, "False");
      Any (Term.not_id,   name, "~");
      Any (Term.not_id,   pos, Pretty.Prefix);
      Any (Term.imply_id, name, "→");
      Any (Term.imply_id, pos, Pretty.Infix);
      Any (Term.equiv_id, name, "↔");
      Any (Term.equiv_id, pos, Pretty.Infix);
      Any (Term.or_id,    name, "∨");
      Any (Term.or_id,    pos, Pretty.Infix);
      Any (Term.or_id,    assoc, Pretty.Left);
      Any (Term.and_id,   name, "∧");
      Any (Term.and_id,   pos, Pretty.Infix);
      Any (Term.and_id,   assoc, Pretty.Left);
    ]

  let t =
    let name = Escape.tagged_name ~tags:[name; Expr.Print.name] in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          if Uchar.equal c (Uchar.of_char '>') then
            [ Uchar.of_char '&';
              Uchar.of_char 'g';
              Uchar.of_char 't';
              Uchar.of_char ';' ]
          else if Uchar.equal c (Uchar.of_char '<') then
            [ Uchar.of_char '&';
              Uchar.of_char 'l';
              Uchar.of_char 't';
              Uchar.of_char ';' ]
          else if Uchar.equal c (Uchar.of_char '&') then
            [ Uchar.of_char '&';
              Uchar.of_char 'a';
              Uchar.of_char 'm';
              Uchar.of_char 'p';
              Uchar.of_char ';' ]
          else if Uchar.equal c (Uchar.of_char '"') then
            [ Uchar.of_char '&';
              Uchar.of_char 'q';
              Uchar.of_char 'u';
              Uchar.of_char 'o';
              Uchar.of_char 't';
              Uchar.of_char ';' ]
          else
            [ c ]
      ) in
    Escape.mk ~lang:"html" ~name ~escape ~rename

  (* Proof term printing *)
  module Proof = struct

    let binder_name = function
      | Term.Lambda -> "λ"
      | Term.Forall -> "∀"
      | Term.Exists -> "∃"

    let binder_sep = function _ -> ","

    let id fmt v =
      Escape.id t fmt v

    let is_equal = Term.equal Term.equal_term

    let get_status = function
      | { Term.term = Term.Id f } ->
        Expr.Id.get_tag f pos
      | _ -> None

    let rec term fmt t =
      match t.Term.term with
      | Term.Type -> Format.fprintf fmt "Type"
      | Term.Id v -> id fmt v
      | Term.App _ ->
        let f, args = Term.uncurry ~assoc t in
        begin match get_status f with
          | _ when is_equal f ->
            begin match args with
              | [_; a; b] ->
                Format.fprintf fmt "@[<hov>%a@ = %a@]" term a term b
              | _ -> assert false
            end
          | None ->
            Format.fprintf fmt "@[<hov>(%a %a)@]" term f
              CCFormat.(list ~sep:(return "@ ") term) args
          | Some Pretty.Prefix ->
            Format.fprintf fmt "@[<hov>%a %a@]" term f
              CCFormat.(list ~sep:(return "@ ") term) args
          | Some Pretty.Infix ->
            let sep fmt () = Format.fprintf fmt "@ %a " term f in
            Format.fprintf fmt "@[<hov>(%a)@]" CCFormat.(list ~sep term) args
        end
      | Term.Let (v, e, body) ->
        Format.fprintf fmt "@[<v>@[<hv>let %a := @[<hov>%a@]@ in@]@ %a@]"
          id v term e term body
      | Term.Binder (b, _, _) ->
        let kind, vars, body = Term.flatten_binder t in
        begin match kind with
          | `Arrow ->
            let tys = List.map (fun id -> id.Expr.id_type) vars in
            Format.fprintf fmt "(@[<hov>%a@ →%a@])"
              CCFormat.(list ~sep:(return "@ → ") term) tys term body
          | `Pi | `Binder _ ->
            let l = Term.concat_vars vars in
            Format.fprintf fmt "(@[<hov 2>%s@[<hov>%a@]%s@ %a@])"
              (binder_name b) var_lists l
              (binder_sep b) term body
        end

    and var_list fmt (ty, l) =
      assert (l <> []);
      Format.fprintf fmt "(%a:@ %a)"
        CCFormat.(list ~sep:(return "@ ") id) l term ty

    and var_lists fmt l =
      CCFormat.(list ~sep:(return "@ ") var_list) fmt l

  end

  open Expr

  let id fmt v =
    Escape.id t fmt v

  let meta fmt m =
    Format.fprintf fmt "m%d_%a"
      ((m.meta_index) : meta_index :> int) id m.meta_id

  let ttype fmt = function Type -> Format.fprintf fmt "Type"

  let rec ty fmt t = match t.ty with
    | TyVar v -> id fmt v
    | TyMeta m -> meta fmt m
    | TyApp (f, []) -> id fmt f
    | TyApp (f, l) ->
      begin match Tag.get f.id_tags Print.pos with
        | None ->
          Format.fprintf fmt "@[<hov 2>%a(%a)@]"
            id f CCFormat.(list ~sep:(return ",") ty) l
        | Some Pretty.Prefix ->
          assert (List.length l = 1);
          Format.fprintf fmt "@[<hov 2>%a %a@]"
            id f CCFormat.(list ~sep:(return "") ty) l
        | Some Pretty.Infix ->
          let sep fmt () = Format.fprintf fmt " %a@ " id f in
          Format.fprintf fmt "@[<hov 2>(%a)@]" (CCFormat.list ~sep ty) l
      end

  (*
  let params fmt = function
    | [] -> ()
    | l -> Format.fprintf fmt "∀ @[<hov>%a@].@ "
             CCFormat.(list ~sep:(return ",@ ") id) l

  let signature print fmt f =
    match f.fun_args with
    | [] -> Format.fprintf fmt "@[<hov 2>%a%a@]" params f.fun_vars print f.fun_ret
    | l -> Format.fprintf fmt "@[<hov 2>%a%a ->@ %a@]" params f.fun_vars
             CCFormat.(list ~sep:(return " ->@ ") print) l print f.fun_ret

  let fun_ty = signature ty
  let fun_ttype = signature ttype
  *)

  let id_pretty fmt v =
    match Tag.get v.id_tags Print.pos with
    | None -> ()
    | Some Pretty.Prefix -> Format.fprintf fmt "[%a]" id v
    | Some Pretty.Infix -> Format.fprintf fmt "(%a)" id v

  let id_type print fmt v =
    Format.fprintf fmt "@[<hov 2>%a%a :@ %a@]" id v id_pretty v print v.id_type

  let id_ty = id_type ty
  let id_ttype = id_type ttype

  let rec term fmt t = match t.term with
    | Var v -> id fmt v
    | Meta m -> meta fmt m
    | App (f, [], []) -> id fmt f
    | App (f, tys, args) ->
      begin match Tag.get f.id_tags Print.pos with
        | None ->
          begin match tys with
            | [] ->
              Format.fprintf fmt "%a(@[<hov>%a@])"
                id f CCFormat.(list ~sep:(return ",@ ") term) args
            | _ ->
              Format.fprintf fmt "%a(@[<hov>%a%a%a@])" id f
                CCFormat.(list ~sep:(return ",@ ") ty) tys
                (CCFormat.return ";@ ") ()
                CCFormat.(list ~sep:(return ",@ ") term) args
          end
        | Some Pretty.Prefix ->
          Format.fprintf fmt "@[<hov>%a(%a)@]"
            id f CCFormat.(list ~sep:(return ",@ ") term) args
        | Some Pretty.Infix ->
          let sep fmt () = Format.fprintf fmt " %a@ " id f in
          Format.fprintf fmt "(%a)" CCFormat.(list ~sep term) args
      end

  let rec formula_aux fmt f =
    let aux fmt f = match f.formula with
      | Equal _ | Pred _ | True | False -> formula_aux fmt f
      | _ -> Format.fprintf fmt "(@ %a@ )" formula_aux f
    in
    match f.formula with
    | Pred t -> Format.fprintf fmt "%a" term t
    | Equal (a, b) -> Format.fprintf fmt "@[<hov>%a@ =@ %a@]" term a term b

    | True  -> Format.fprintf fmt "⊤"
    | False -> Format.fprintf fmt "⊥"
    | Not f -> Format.fprintf fmt "@[<hov 2>¬ %a@]" aux f
    | And l -> Format.fprintf fmt "@[<hov>%a@]"
                 CCFormat.(list ~sep:(return " ∧@ ") aux) l
    | Or l  -> Format.fprintf fmt "@[<hov>%a@]"
                 CCFormat.(list ~sep:(return " ∨@ ") aux) l

    | Imply (p, q)    -> Format.fprintf fmt "@[<hov>%a@ ⇒@ %a@]" aux p aux q
    | Equiv (p, q)    -> Format.fprintf fmt "@[<hov>%a@ ⇔@ %a@]" aux p aux q

    | All ((l, []), _, f) ->
      Format.fprintf fmt "@[<hv 2>∀ @[<hov>%a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ttype) l formula_aux f
    | All (([], l), _, f) ->
      Format.fprintf fmt "@[<hv 2>∀ @[<hov>%a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ty) l formula_aux f
    | All ((tys,ts), _, f) ->
      Format.fprintf fmt "@[<hv 2>∀ @[<hov>%a,@ %a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ttype) tys
        CCFormat.(list ~sep:(return ",@ ") id_ty) ts formula_aux f
    | Ex ((l, []), _, f) ->
      Format.fprintf fmt "@[<hv 2>∃ @[<hov>%a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ttype) l formula_aux f
    | Ex (([], l), _, f) ->
      Format.fprintf fmt "@[<hv 2>∃ @[<hov>%a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ty) l formula_aux f
    | Ex ((tys,ts), _, f) ->
      Format.fprintf fmt "@[<hv 2>∃ @[<hov>%a,@ %a@].@ %a@]"
        CCFormat.(list ~sep:(return ",@ ") id_ttype) tys
        CCFormat.(list ~sep:(return ",@ ") id_ty) ts formula_aux f

  let formula fmt f = Format.fprintf fmt "⟦@[<hov>%a@]⟧" formula_aux f

  let mapping fmt m =
    Mapping.fold m ()
      ~ty_var:(fun v t () -> Format.fprintf fmt "%a ↦ %a;@ " id v ty t)
      ~ty_meta:(fun m t () -> Format.fprintf fmt "%a ↦ %a;@ " meta m ty t)
      ~term_var:(fun v t () -> Format.fprintf fmt "%a ↦ %a;@ " id v term t)
      ~term_meta:(fun m t () -> Format.fprintf fmt "%a ↦ %a;@ " meta m term t)

end

(* Printing wrappers *)
(* ************************************************************************ *)

let buffer = Buffer.create 1013

let sfmt =
  let fmt = Format.formatter_of_buffer buffer in
  let f = Format.pp_get_formatter_out_functions fmt () in
  let () = Format.pp_set_formatter_out_functions fmt
      Format.{ f with out_newline = function () ->
          f.out_string {|<br align="left" />|} 0 19}
  in
  fmt

let box pp = fun fmt x ->
  let () = Buffer.clear buffer in
  let () = Format.fprintf sfmt "%a@?" pp x in
  let s = Buffer.contents buffer in
  Format.fprintf fmt "%s" s

(* Printing functor argument *)
(* ************************************************************************ *)

type _ D.msg +=
  | Info : D.lemma_info ->
    (string option * ((Format.formatter -> unit -> unit) list)) D.msg

module Arg = struct

  let print_atom fmt a =
    let f = a.Dispatcher.SolverTypes.lit in
    box Print.formula fmt f

  let hyp_info c =
    let id = Solver.hyp_proof c in
    "Hypothesis", Some "YELLOW",
    [fun fmt () -> Print.id fmt (id :> Term.t Expr.id)]

  let lemma_info c =
    let lemma =
      match c.Dispatcher.SolverTypes.cpremise with
      | Dispatcher.SolverTypes.Lemma l -> l
      | _ -> assert false
    in
    let name = Format.sprintf "%s/%s" lemma.D.plugin_name lemma.D.proof_name in
    let color, fmts =
      match D.ask lemma.D.plugin_name (Info lemma.D.proof_info) with
      | Some r -> r
      | None ->
        Util.warn ~section "Got no lemma info from plugin %s for proof %s"
          lemma.D.plugin_name lemma.D.proof_name;
        Some "WHITE", [fun fmt () -> Format.fprintf fmt "N/A"]
    in
    name, color, List.map box fmts

  let assumption_info c =
    "assumption", Some "YELLOW", []

end

module P = Msat.Dot.Make(Solver.Proof)(Arg)

let print = P.print

(* Initialization & proof context *)
(* ************************************************************************ *)

let init_full fmt opt =
  Format.fprintf fmt
    "@\n/*@[<v>@ %s@ Input file: %s@]@ */@]@\n@."
    "Proof automatically generated by Archsat"
    Options.(input_to_string opt.input.file)

let proof_context pp fmt x =
  Format.fprintf fmt "digraph proof {@\n%a}@." pp x

