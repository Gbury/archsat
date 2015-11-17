%{
    module L = ParseLocation
    let sexpr = Ast.const (Ast.sym "Sexpr")
    let sexpr_list = Ast.const (Ast.sym "Sexpr-list")

    let assert_name =
      let i = ref 0 in
      (fun () -> incr i; "hyp" ^ (string_of_int !i))

    let translate_fun_sym = function
    | "true" -> Ast.True
    | "false" -> Ast.False
    | "not" -> Ast.Not
    | "=>" -> Ast.Imply
    | "and" -> Ast.And
    | "or" -> Ast.Or
    | "xor" -> Ast.Xor
    | "=" -> Ast.Eq
    | "distinct" -> Ast.Distinct
    | "ite" -> Ast.Ite
    | s -> Ast.sym s

    let fun_symbol = function
    | { Ast.term = Ast.Const Ast.String s; Ast.loc = l } ->
      begin match l with
      | Some loc -> Ast.const ~loc (translate_fun_sym s)
      | None -> Ast.const (translate_fun_sym s)
      end
    | s -> s

%}

%token EOF

%token OPEN CLOSE
%token <string> NUMERAL DECIMAL HEXADECIMAL BINARY STRING SYMBOL KEYWORD

%token UNDERSCORE

%token AS

%token LET FORALL EXISTS ATTRIBUTE

%token SET_LOGIC SET_OPTION SET_INFO DECLARE_SORT DEFINE_SORT DECLARE_FUN 
DEFINE_FUN PUSH POP ASSERT CHECK_SAT GET_ASSERTIONS GET_PROOF GET_UNSAT_CORE 
GET_VALUE GET_ASSIGNMENT GET_OPTION GET_INFO EXIT

%start <Ast.term> term
%start <Ast.command list> file
%start <Ast.command list option> input

%%

numeral_plus:
  | NUMERAL                 { $1 }
  | NUMERAL numeral_plus    { $1 ^ "_" ^ $2 }
;

symbol_star:
  |                       { [] }
  | SYMBOL symbol_star    { (Ast.const (Ast.sym $1)) :: $2 }
;

spec_constant:
  | NUMERAL        { Ast.int $1 }
  | DECIMAL        { Ast.real $1 }
  | HEXADECIMAL    { Ast.hexa $1 }
  | BINARY         { Ast.binary $1 }
  | STRING         { Ast.sym $1 }
;

s_expr:
  | spec_constant             { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $1 }
  | SYMBOL                    { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc (Ast.sym $1) }
  | KEYWORD                   { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc (Ast.sym $1) }
  | OPEN s_expr_star CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.app ~loc sexpr $2 }
;

s_expr_star:
  |                       { [] }
  | s_expr s_expr_star    { $1 :: $2 }
;

identifier:
  | SYMBOL                                       { Ast.sym $1 }
  | OPEN UNDERSCORE SYMBOL numeral_plus CLOSE    { Ast.sym ($3 ^ "_" ^ $4) }
;

sort:
  | identifier                         { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $1 }
  | OPEN identifier sort_plus CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.app ~loc (Ast.const $2) $3 }
;

sort_star:
  |                   { [] }
  | sort sort_star    { $1 :: $2 }
;

sort_plus:
  | sort              { [$1] }
  | sort sort_plus    { $1 :: $2 }
;

attribute_value:
  | spec_constant             { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $1 }
  | SYMBOL                    { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc (Ast.sym $1) }
  | OPEN s_expr_star CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.app ~loc sexpr_list $2 }
;

attribute:
  | KEYWORD                    { ($1,None) }
  | KEYWORD attribute_value    { ($1,Some $2) }
;

attribute_plus:
  | attribute                   { [$1] }
  | attribute attribute_plus    { $1 :: $2 }
;

qual_identifier:
  | identifier                       { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $1 }
  | OPEN AS identifier sort CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $3 }
;

var_binding:
  | OPEN SYMBOL term CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.var ~loc ~ty:$3 $2 }
;

var_binding_plus:
  | var_binding                     { [$1] }
  | var_binding var_binding_plus    { $1 :: $2 }
;

sorted_var:
  | OPEN SYMBOL sort CLOSE      { let loc = L.mk_pos $startpos $endpos in Ast.var ~loc ~ty:$3 $2 }
;

sorted_var_star:
  |                               { [] }
  | sorted_var sorted_var_star    { $1 :: $2 }
;

sorted_var_plus:
  | sorted_var                    { [$1] }
  | sorted_var sorted_var_plus    { $1 :: $2 }
;

term:
  | spec_constant                                        { let loc = L.mk_pos $startpos $endpos in Ast.const ~loc $1 }
  | qual_identifier                                      { let loc = L.mk_pos $startpos $endpos in Ast.app ~loc (fun_symbol $1) [] }
  | OPEN qual_identifier term_plus CLOSE                 { let loc = L.mk_pos $startpos $endpos in Ast.app ~loc (fun_symbol $2) $3 }
  | OPEN LET OPEN var_binding_plus CLOSE term CLOSE      { let loc = L.mk_pos $startpos $endpos in Ast.letin ~loc $4 $6 }
  | OPEN FORALL OPEN sorted_var_plus CLOSE term CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.forall ~loc $4 $6 }
  | OPEN EXISTS OPEN sorted_var_plus CLOSE term CLOSE    { let loc = L.mk_pos $startpos $endpos in Ast.exists ~loc $4 $6 }
  | OPEN ATTRIBUTE term attribute_plus CLOSE             { $3 }
;

term_plus:
  | term              { [$1] }
  | term term_plus    { $1 :: $2 }
;

command_option:
  | attribute    { $1 }
;

info_flag:
  | KEYWORD    { $1 }
;

command:
  | OPEN SET_LOGIC SYMBOL CLOSE                                         { [] }
  | OPEN SET_OPTION command_option CLOSE                                { [] }
  | OPEN SET_INFO attribute CLOSE                                       { [] }
  | OPEN DECLARE_SORT SYMBOL NUMERAL CLOSE                              { [Ast.NewType ($3, Ast.sym $3, int_of_string $4)] }
  | OPEN DEFINE_SORT SYMBOL OPEN symbol_star CLOSE sort CLOSE           { [Ast.TypeAlias (Ast.sym $3, $5, $7)] }
  | OPEN DECLARE_FUN SYMBOL OPEN sort_star CLOSE sort CLOSE             { [Ast.TypeDef ($3, Ast.sym $3, Ast.mk_fun_ty $5 $7)] }
  | OPEN DEFINE_FUN SYMBOL OPEN sorted_var_star CLOSE sort term CLOSE   { [Ast.Alias (Ast.sym $3, $5, Ast.column $7 $8)] }
  | OPEN PUSH NUMERAL CLOSE                                             { CCList.replicate (int_of_string $3) Ast.Push }
  | OPEN POP NUMERAL CLOSE                                              { CCList.replicate (int_of_string $3) Ast.Pop }
  | OPEN ASSERT term CLOSE                                              { [Ast.Assert (assert_name (), $3, false)] }
  | OPEN CHECK_SAT CLOSE                                                { [Ast.CheckSat] }
  | OPEN GET_ASSERTIONS CLOSE                                           { [] }
  | OPEN GET_PROOF CLOSE                                                { [] }
  | OPEN GET_UNSAT_CORE CLOSE                                           { [] }
  | OPEN GET_VALUE OPEN term_plus CLOSE CLOSE                           { [] }
  | OPEN GET_ASSIGNMENT CLOSE                                           { [] }
  | OPEN GET_OPTION KEYWORD CLOSE                                       { [] }
  | OPEN GET_INFO info_flag CLOSE                                       { [] }
  | OPEN EXIT CLOSE                                                     { [] }
;

file:
  | EOF { [] }
  | command file { $1 @ $2 }
;

input:
  | EOF { None }
  | command { Some $1 }

%%
