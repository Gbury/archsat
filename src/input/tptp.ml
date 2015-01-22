
(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBBTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BBT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBBTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BBT NOT LIMITED TO, PROCUREMENT OF SUBSTITBTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OBT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 Utils related to TPTP parsing} *)

module A = Ast_tptp
module AU = A.Untyped
module Loc = ParseLocation

exception Parse_error of Loc.t * string
exception Syntax_error of string

let log_section = Util.Section.make "tptp"
let log i fmt = Util.debug ~section:log_section i fmt

(** {2 Translation} *)
let t_assert name t = Ast.Assert (A.string_of_name name, t)

let arity_of_type_constr s = function
    | { Ast.term = Ast.Const Ast.Ttype } -> 0
    | { Ast.term = Ast.App ({Ast.term = Ast.Const Ast.Arrow}, l) } ->
      List.iter (fun t -> if not (Ast.(t.term) = Ast.Const Ast.Ttype)
        then raise (Syntax_error ("Ill-formed new type declaration for " ^ s))) l;
      List.length l - 1
    | t ->
      log 0 "Expected new type, received : %a" Ast.debug_term t;
      raise (Syntax_error ("Ill-formed new type declaration for : " ^ s))

let translate q = function
  | AU.FOF (name, (A.R_axiom | A.R_hypothesis), t, _)
  | AU.TFF (name, (A.R_axiom | A.R_hypothesis), t, _) ->
    Queue.push (t_assert name t) q
  | AU.FOF (name, (A.R_assumption | A.R_lemma | A.R_theorem), t, _)
  | AU.TFF (name, (A.R_assumption | A.R_lemma | A.R_theorem), t, _) ->
    Queue.push Ast.Push q;
    Queue.push (t_assert name (Ast.not_ t)) q;
    Queue.push Ast.CheckSat q;
    Queue.push Ast.Pop q;
    Queue.push (t_assert name (Ast.not_ t)) q
  | AU.FOF (name, A.R_conjecture, t, _)
  | AU.TFF (name, A.R_conjecture, t, _) ->
    Queue.push (t_assert name (Ast.not_ t)) q;
    Queue.push Ast.CheckSat q
  | AU.FOF (name, A.R_negated_conjecture, t, _)
  | AU.TFF (name, A.R_negated_conjecture, t, _) ->
    Queue.push (t_assert name t) q;
    Queue.push Ast.CheckSat q
  | AU.NewType (name, s, t) ->
    let n = arity_of_type_constr s t in
    Queue.push (Ast.NewType (A.string_of_name name, Ast.sym s, n)) q
  | AU.TypeDecl (name, s, t) ->
    Queue.push (Ast.TypeDef (A.string_of_name name, Ast.sym s, t)) q
  | _ ->
    log 0 "Couldn't translate a command"

(** {2 Parsing} *)

let find_file name dir =
  (* check if the file exists *)
  let file_exists name =
    try ignore (Unix.stat name); true
    with Unix.Unix_error (e, _, _) when e = Unix.ENOENT -> false
  in
  (* search in [dir], and its parents recursively *)
  let rec search dir =
    let cur_name = Filename.concat dir name in
    log 2 "search %s as %s" name cur_name;
    if file_exists cur_name
    then Some cur_name
    else
      let dir' = Filename.dirname dir in
      if dir = dir'
      then None
      else search dir'
  in
  let search_env () =
    try
      let dir' = Sys.getenv "TPTP" in
      search dir'
    with Not_found -> None
  in
  if Filename.is_relative name
  (* search by relative path, in parent dirs *)
  then match search dir with
    | None -> search_env ()
    | Some _ as res -> res
  else if file_exists name
  then Some name  (* found *)
  else None

(* raise a readable parse error *)
let _raise_error msg lexbuf =
  let loc = Loc.of_lexbuf lexbuf in
  raise (Parse_error (loc, msg))

(* find file *)
let _find_and_open filename dir =
  match filename with
  | "stdin" -> stdin
  | _ ->
    match find_file filename dir with
    | Some filename ->
      begin try open_in filename
        with Sys_error msg ->
          failwith ("error when opening file " ^ filename ^ " : " ^ msg)
      end
    | None -> failwith ("could not find file " ^ filename)

let parse_file ~recursive f =
  let dir = Filename.dirname f in
  let result_decls = Queue.create () in
  (* function that parses one file *)
  let rec parse_this_file ?names filename =
    (* find and open file *)
    let input = _find_and_open filename dir in
    try
      let buf = Lexing.from_channel input in
      Loc.set_file buf filename;
      (* parse declarations from file *)
      let decls =
        try Parsetptp.parse_declarations Lextptp.token buf
        with
        | Parsetptp.Error -> _raise_error "parse error at " buf
        | Ast_tptp.ParseError loc -> raise (Parse_error (loc, "parse error"))
      in
      List.iter
        (fun decl -> match decl, names with
           | (AU.CNF _ | AU.FOF _ | AU.TFF _ | AU.THF _ | AU.TypeDecl _ | AU.NewType _), None ->
             Queue.push decl result_decls
           | (AU.CNF _ | AU.FOF _ | AU.TFF _ | AU.THF _ | AU.TypeDecl _ | AU.NewType _), Some names ->
             if List.mem (AU.get_name decl) names
             then Queue.push decl result_decls
             else ()   (* not included *)
           | AU.Include f, _ when recursive ->
             parse_this_file ?names:None f
           | AU.IncludeOnly (f, names'), _ when recursive ->
             parse_this_file ~names:names' f
           | (AU.Include _ | AU.IncludeOnly _), _ ->
             Queue.push decl result_decls)
        decls
    with e ->
      close_in input;
      raise e
  in
  parse_this_file ?names:None (Filename.basename f);
  let res = Queue.create () in
  Queue.iter (translate res) result_decls;
  res

