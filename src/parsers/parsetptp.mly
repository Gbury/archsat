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

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 TTP Parser} *)

%{
  module L = ParseLocation
  module A = Ast_tptp.Untyped
  module T = Ast

  let remove_quotes s =
    assert (s.[0] = '\'' && s.[String.length s - 1] = '\'');
    String.sub s 1 (String.length s - 2)
%}

%token EOI

%token DOT
/* %token SEMICOLUMN */
%token COMMA
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_BRACKET
%token RIGHT_BRACKET

%token FOF
%token CNF
%token TFF
%token INCLUDE

%token NOT

%token COLUMN
%token STAR
%token ARROW
%token FORALL_TY  /* quantification on types */
%token TYPE_TY  /* tType */
%token WILDCARD  /* $_ */

%token AND
%token NOTAND
%token VLINE
%token NOTVLINE
%token IMPLY
%token LEFT_IMPLY
%token EQUIV
%token XOR
%token GENTZEN_ARROW
%token EQUAL
%token NOT_EQUAL

%token TRUE
%token FALSE

%token FORALL
%token EXISTS

%token UNDERSCORE

%token <string> LOWER_WORD
%token <string> UPPER_WORD
%token <string> SINGLE_QUOTED
%token <string> DISTINCT_OBJECT
%token <string> DOLLAR_WORD
%token <string> DOLLAR_DOLLAR_WORD
%token <string> REAL
%token <string> RATIONAL
%token <string> INTEGER

%left VLINE
%left AND
%nonassoc EQUIV
%nonassoc XOR
%nonassoc IMPLY
%nonassoc LEFT_IMPLY
%nonassoc NOTVLINE
%nonassoc NOTAND

%start <Ast_tptp.Untyped.declaration> declaration
%start <Ast_tptp.Untyped.declaration list> file

%%

/* Complete file, i.e Top-level declarations */

file: l=declarations EOI { l }

/* TTP grammar */

declarations:
  | l=declaration* { l }

declaration:
  | FOF LEFT_PAREN name=name COMMA role=role COMMA f=fof_formula info=annotations RIGHT_PAREN DOT
    { A.FOF (name, role, f, info) }
  | TFF LEFT_PAREN name=name COMMA role=role COMMA f=fof_formula info=annotations RIGHT_PAREN DOT
    { A.TFF (name, role, f, info) }
  | TFF LEFT_PAREN name=name COMMA role COMMA tydecl=type_decl info=annotations RIGHT_PAREN DOT
    { let s, ty = tydecl in
      match ty.T.term with
      | T.Const T.Ttype
      | T.App ({T.term = T.Const (T.Arrow)},
               ({T.term = T.Const (T.Ttype)} :: _)) ->
        (* declare a new type symbol *)
        A.NewType (name, s, ty)
      | _ -> A.TypeDecl (name, s, ty)
    }
  | CNF LEFT_PAREN name=name COMMA role=role COMMA c=cnf_formula info=annotations RIGHT_PAREN DOT
    { A.CNF (name, role, c, info) }
  | INCLUDE LEFT_PAREN x=SINGLE_QUOTED RIGHT_PAREN DOT
    { A.Include (remove_quotes x) }
  | INCLUDE LEFT_PAREN x=SINGLE_QUOTED COMMA names=name_list RIGHT_PAREN DOT
    { A.IncludeOnly (x, names) }
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (Ast_tptp.ParseError loc)
    }

role: w=LOWER_WORD { Ast_tptp.role_of_string w }

type_decl:
  | LEFT_PAREN tydecl=type_decl RIGHT_PAREN { tydecl }
  | s=atomic_word COLUMN ty=tff_quantified_type { s, ty }
  | s=DOLLAR_WORD COLUMN ty=tff_quantified_type { s, ty }

cnf_formula:
  | LEFT_PAREN c=disjunction RIGHT_PAREN { c }
  | c=disjunction { c }

disjunction:
  | l=separated_nonempty_list(VLINE, literal) { l }

literal:
  | f=atomic_formula { f }
  | NOT f=atomic_formula
    {
      let loc = L.mk_pos $startpos $endpos in
      T.not_ ~loc f
    }

fof_formula:
  | fof_logic_formula { $1 }
  | fof_sequent { $1 }

fof_sequent:
  | l=fof_tuple GENTZEN_ARROW r=fof_tuple
    { (* TODO accurate locs for subterms *)
      let loc = L.mk_pos $startpos $endpos in
      T.imply ~loc (T.and_ ~loc l) (T.or_ ~loc r)
    }
  | LEFT_PAREN seq=fof_sequent RIGHT_PAREN { seq }

fof_tuple:
  LEFT_BRACKET l=separated_list(COMMA, fof_logic_formula) RIGHT_BRACKET { l } 

fof_logic_formula:
  | f=fof_unitary_formula { f }
  | l=fof_logic_formula o=binary_connective r=fof_logic_formula
    {
      let loc = L.mk_pos $startpos $endpos in
      o ?loc:(Some loc) l r
    }

fof_unitary_formula:
  | fof_quantified_formula { $1 }
  | fof_unary_formula { $1 }
  | atomic_formula { $1 }
  | LEFT_PAREN f=fof_logic_formula RIGHT_PAREN { f }

fof_quantified_formula:
  | q=fol_quantifier LEFT_BRACKET vars=variables RIGHT_BRACKET COLUMN f=fof_unitary_formula
    {
      let loc = L.mk_pos $startpos $endpos in
      q ~loc vars f
    }

fof_unary_formula:
  | o=unary_connective f=fof_unitary_formula
    {
     let loc = L.mk_pos $startpos $endpos in
     o ~loc f
    }

%inline binary_connective:
  | EQUIV { T.equiv }
  | IMPLY { T.imply }
  | LEFT_IMPLY { fun ?loc l r -> T.imply ?loc r l }
  | XOR { T.xor }
  | NOTVLINE { fun ?loc x y -> T.not_ ?loc (T.or_ ?loc [x; y]) }
  | NOTAND { fun ?loc x y -> T.not_ ?loc (T.and_ ?loc [x; y]) }
  | AND { fun ?loc x y -> T.and_ ?loc [x;y] }
  | VLINE { fun ?loc x y -> T.or_ ?loc [x;y] }
%inline fol_quantifier:
  | FORALL { T.forall }
  | EXISTS { T.exists }
%inline unary_connective:
  | NOT { T.not_ }

atomic_formula:
  | TRUE  { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc T.true_ }
  | FALSE { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc T.false_ }
  | l=term o=infix_connective r=term
    { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc (o l r) }
  | t=function_term
    { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc t }

%inline infix_connective:
  | EQUAL { T.eq }
  | NOT_EQUAL { T.neq }

/* Terms */

term:
  | function_term { $1 }
  | variable { $1 }
  /* | conditional_term { $1 }  for TFF */
  /* | let_term { $1 } */

function_term:
  | plain_term { $1 }
  | defined_term { $1 }
  | system_term { $1 }

plain_term:
  | s=constant
    {
      let loc = L.mk_pos $startpos $endpos in
      T.const ~loc s
    }
  | f=functor_ LEFT_PAREN args=arguments RIGHT_PAREN
    {
      let loc = L.mk_pos $startpos $endpos in
      T.app ~loc f args
    }

constant:
| s=atomic_word { T.sym s }
| s=atomic_defined_word { s }
functor_: f=atomic_word
{ let loc = L.mk_pos $startpos $endpos in T.const ~loc (T.sym f) }

defined_term:
  | t=defined_atom
    {
      let loc = L.mk_pos $startpos $endpos in
      T.const ~loc t
    }
  | t=defined_atomic_term { t }

defined_atom:
  | n=INTEGER { T.int n }
  | n=RATIONAL { T.rat n }
  | n=REAL { T.real n }
  | DISTINCT_OBJECT { T.distinct }

defined_atomic_term:
  | t=defined_plain_term { t }
  /* | defined_infix_term { $1 } */

defined_plain_term:
  | s=defined_constant
    {
      let loc = L.mk_pos $startpos $endpos in
      T.const ~loc s
    }
  | f=defined_functor LEFT_PAREN args=arguments RIGHT_PAREN
    {
      let loc = L.mk_pos $startpos $endpos in
      T.app ~loc (T.const f) args
    }

defined_constant: t=defined_functor { t }
defined_functor: s=atomic_defined_word { s }

system_term:
  | c=system_constant
    {
      let loc = L.mk_pos $startpos $endpos in
      T.const ~loc c
    }
  | f=system_functor LEFT_PAREN args=arguments RIGHT_PAREN
    {
      let loc = L.mk_pos $startpos $endpos in
      T.app ~loc (T.const f) args
    }

system_constant: t=system_functor { t }
system_functor: s=atomic_system_word { s }

/* prenex quantified type */
tff_quantified_type:
  | ty=tff_type { ty }
  | FORALL_TY LEFT_BRACKET vars=tff_ty_vars RIGHT_BRACKET COLUMN ty=tff_quantified_type
    { T.forall_ty vars ty }

/* general type, without quantifiers */
tff_type:
  | ty=tff_atom_type { ty }
  | l=tff_atom_type ARROW r=tff_atom_type
    { T.mk_fun_ty [l] r }
  | LEFT_PAREN args=tff_ty_args RIGHT_PAREN ARROW r=tff_atom_type
    { T.mk_fun_ty args r }

tff_atom_type:
  | UNDERSCORE { let loc = L.mk_pos $startpos $endpos in T.const ~loc T.wildcard }
  | v=tff_ty_var { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc v }
  | w=type_const { let loc = L.mk_pos $startpos $endpos in T.const ~loc w }
  | w=type_const LEFT_PAREN l=separated_nonempty_list(COMMA, tff_type) RIGHT_PAREN
    { let loc = L.mk_pos $startpos $endpos in T.app ~loc (T.const w) l }
  | TYPE_TY { let loc = L.mk_pos $startpos $endpos in T.at_loc ~loc T.tType }
  | LEFT_PAREN ty=tff_type RIGHT_PAREN { ty }

tff_ty_args:
  | ty=tff_atom_type { [ty] }
  | hd=tff_atom_type STAR tl=tff_ty_args { hd :: tl }

tff_ty_vars:
  | v=tff_ty_var COLUMN TYPE_TY {  [v] }
  | v=tff_ty_var COLUMN TYPE_TY COMMA l=tff_ty_vars { v::l }

tff_ty_var: w=UPPER_WORD { let loc = L.mk_pos $startpos $endpos in T.var ~loc w }

type_const:
  | WILDCARD { T.wildcard }
  | w=LOWER_WORD { T.sym w }
  | w=DOLLAR_WORD { T.sym w }

arguments: separated_nonempty_list(COMMA, term) { $1 }

variables:
  | l=separated_nonempty_list(COMMA, variable) { l }

variable:
  | x=UPPER_WORD
    {
      let loc = L.mk_pos $startpos $endpos in
      T.var ~loc x
    }
  | x=UPPER_WORD COLUMN ty=tff_type
    {
      let loc = L.mk_pos $startpos $endpos in
      T.var ~loc ~ty x
    }

atomic_word:
  | s=SINGLE_QUOTED { remove_quotes s }
  | s=LOWER_WORD { s }

atomic_defined_word:
  | WILDCARD { T.wildcard }
  | w=DOLLAR_WORD { T.sym w }

atomic_system_word:
  | w=DOLLAR_DOLLAR_WORD { T.sym w }

name_list:
  l=separated_list(COMMA, name) { l }

name:
  | w=atomic_word { Ast_tptp.NameString w }
  | i=INTEGER { Ast_tptp.NameInt (int_of_string i) }

annotations:
  | { [] }
  | COMMA l=separated_list(COMMA, general_term) { l }

general_term:
  | general_data { $1 }
  | l=general_data COLUMN r=general_term { Ast_tptp.GColumn (l, r) }
  | general_list { $1 }

general_data:
  | w=atomic_word { Ast_tptp.GString w }
  | general_function { $1 }
  | i=INTEGER { Ast_tptp.GInt (int_of_string i) }
  | v=UPPER_WORD { Ast_tptp.GVar v }
  | w=DISTINCT_OBJECT { Ast_tptp.GString w }

general_function:
  | f=atomic_word LEFT_PAREN l=separated_nonempty_list(COMMA, general_term) RIGHT_PAREN
    { Ast_tptp.GNode (f, l) }

general_list:
  | LEFT_BRACKET l=separated_list(COMMA, general_term) RIGHT_BRACKET
    { Ast_tptp.GList l }

%%
