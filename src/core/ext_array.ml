(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let name = "array"
let section = Section.make ~parent:Dispatcher.section name

(* Options *)
(* ************************************************************************ *)

type mode =
  | Axiom

let mode_list = [
  "axiom", Axiom;
]

let mode_conv = Cmdliner.Arg.enum mode_list

(* Global state *)
(* ************************************************************************ *)

let mode = ref None

(* Proofs *)
(* ************************************************************************ *)

type info = TODO

type Dispatcher.lemma_info += Array of info

(* Axioms (in smtlib syntax / dolmen terms) *)
(* ************************************************************************ *)

module I = Dolmen.Id
module T = Dolmen.Term

let array_t = T.const @@ I.mk I.sort "Array"
let store_t = T.const @@ I.mk I.term "store"
let select_t = T.const @@ I.mk I.term "select"

let ax_array_eq =
  let key = T.var @@ I.mk I.sort "key" in
  let elem = T.var @@ I.mk I.sort "elem" in
  let a = T.apply array_t [key; elem] in
  let s = T.var @@ I.mk I.term "s" in
  let t = T.var @@ I.mk I.term "t" in
  let i = T.var @@ I.mk I.term "i" in
  let q =
    T.forall [T.colon i key] @@
    T.eq (T.apply select_t [s; i]) (T.apply select_t [t; i])
  in
  let q = T.annot q [T.const I.rwrt_rule] in
  let res =
    T.forall [T.colon key (T.tType ());
              T.colon elem (T.tType ());
              T.colon s a; T.colon t a] @@
    T.equiv (T.eq s t) q
  in
  T.annot res [T.const I.rwrt_rule]

let ax_select_eq =
  let key = T.var @@ I.mk I.sort "key" in
  let elem = T.var @@ I.mk I.sort "elem" in
  let a = T.apply array_t [key; elem] in
  let t = T.var @@ I.mk I.term "t" in
  let i = T.var @@ I.mk I.term "i" in
  let j = T.var @@ I.mk I.term "j" in
  let x = T.var @@ I.mk I.term "x" in
  let res =
    T.forall [T.colon key (T.tType ());
              T.colon elem (T.tType ());
              T.colon t a; T.colon x elem;
              T.colon i key; T.colon j key] @@
    T.imply (T.eq i j) (
      T.eq
        (T.apply select_t [T.apply store_t [t; i; x]; j])
        x
    ) in
  T.annot res [T.const I.rwrt_rule]


let ax_select_neq =
  let key = T.var @@ I.mk I.sort "key" in
  let elem = T.var @@ I.mk I.sort "elem" in
  let a = T.apply array_t [key; elem] in
  let t = T.var @@ I.mk I.term "t" in
  let i = T.var @@ I.mk I.term "i" in
  let j = T.var @@ I.mk I.term "j" in
  let x = T.var @@ I.mk I.term "x" in
  let res =
    T.forall [T.colon key (T.tType ());
              T.colon elem (T.tType ());
              T.colon t a; T.colon x elem;
              T.colon i key; T.colon j key] @@
    T.imply (T.not_ @@ T.eq i j) (
      T.eq
        (T.apply select_t [T.apply store_t [t; i; x]; j])
        (T.apply select_t [t; j])
    ) in
  T.annot res [T.const I.rwrt_rule]


(* Handler & Plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | _ -> None

let options =
  let docs = Options.ext_sect in
  let aux m = mode := m in
  let mode =
    let doc = Format.asprintf
        "Choose the array theory mode. May be %s"
        (Cmdliner.Arg.doc_alts_enum ~quoted:true mode_list) in
    Cmdliner.Arg.(value & opt (some mode_conv) None & info ["array.mode"] ~docs ~doc)
  in
  Cmdliner.Term.(pure aux $ mode)

let hyps () =
  match !mode with
  | Some Axiom -> [
      Dolmen.Statement.rewrite ax_array_eq;
      Dolmen.Statement.rewrite ax_select_eq;
      Dolmen.Statement.rewrite ax_select_neq;
    ]
  | None -> []

let register () =
  Dispatcher.Plugin.register name ~options
    ~descr:"Theory of functional polymorphic arrays"
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ())

