/********************************************************
   This file is part of coreStar
	src/parsing/jparser.mly
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************/

%{ (* header *)

open Corestar_std
open Format

module C = Core

let pp_pos f pos =
  let line = pos.Lexing.pos_lnum in
  let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
  fprintf f "%d:%d" line column

let message prefix text =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  let fn = from_option "<unknown file>" !Load.file_name in
  eprintf "@{<b>%s: %s:(%a)-(%a):@} %s@\n"
    prefix fn pp_pos start_pos pp_pos end_pos text

let parse_error = message "E"
let parse_warning = message "W"

let z3_ctx = Syntax.z3_ctx

let int_sort = Z3.Arithmetic.Integer.mk_sort z3_ctx
let bool_sort = Z3.Boolean.mk_sort z3_ctx

let mk_int_var v = Z3.Expr.mk_const_s z3_ctx v int_sort
let mk_bool_var v = Z3.Expr.mk_const_s z3_ctx v bool_sort
let mk_int_app op args =
  let fdecl = Z3.FuncDecl.mk_func_decl_s z3_ctx op
    (List.map (fun _ -> int_sort) args) int_sort in
  Z3.Expr.mk_app z3_ctx fdecl args
let mk_bool_app op args =
  let fdecl = Z3.FuncDecl.mk_func_decl_s z3_ctx op
    (List.map (fun _ -> int_sort) args) bool_sort in
  Z3.Expr.mk_app z3_ctx fdecl args

let mk_string_const s =
  ignore (Syntax.mk_string_const s);
  Z3.Expr.mk_const_s z3_ctx s int_sort


%} /* declarations */

/* ============================================================= */
/* tokens */
%token ASSIGN
%token BANG
%token CALL
%token CMP_GE
%token CMP_GT
%token CMP_LE
%token CMP_LT
%token COLON
%token COLON_EQUALS
%token COMMA
%token DOT
%token EMP
%token END
%token EOF
%token EQUALS
%token FALSE
%token GLOBAL
%token GOTO
%token IDENTIFIER
%token IF
%token IMPORT
%token INT_CONSTANT
%token LABEL
%token L_BRACE
%token L_BRACKET
%token L_PAREN
%token MULT
%token NOP
%token NOT_EQUALS
%token OP_DIV
%token OP_MINUS
%token OP_PLUS
%token OROR
%token PROCEDURE
%token QUESTIONMARK
%token RULE
%token R_BRACE
%token R_BRACKET
%token R_PAREN
%token SEMICOLON
%token STRING_CONSTANT
%token VDASH

/* types */
%type <string> IDENTIFIER
%type <string> INT_CONSTANT
%type <string> STRING_CONSTANT

/* associativity and precedence */

%left IDENTIFIER
%left OROR
%left MULT

/* entry point */
%start file
%type <ParserAst.entry Load.entry list> file

%% /* rules */

/* Identifiers and constants */

identifier:
  | IDENTIFIER { $1 }
;

qidentifier:
  | QUESTIONMARK IDENTIFIER { "?" ^ $2 }

binop:
  | OP_MINUS { Z3.Arithmetic.mk_sub z3_ctx }
  | OP_PLUS { Z3.Arithmetic.mk_add z3_ctx }
;

cmpop:
  | CMP_LE { Z3.Arithmetic.mk_le z3_ctx }
  | CMP_LT { Z3.Arithmetic.mk_lt z3_ctx }
  | CMP_GE { Z3.Arithmetic.mk_ge z3_ctx }
  | CMP_GT { Z3.Arithmetic.mk_gt z3_ctx }
;


/* Expressions */

identifier_list_ne:
  | identifier { [ $1 ] }
  | identifier COMMA identifier_list_ne { $1 :: $3 }
;

lvariable:
  | identifier { mk_int_var $1 }
  | qidentifier { mk_int_var $1 }
;
lvariable_list_ne:
  |  lvariable    { [$1] }
  |  lvariable COMMA lvariable_list_ne  { $1 :: $3 }
;
lvariable_list:
  |  {[]}
  | lvariable_list_ne { $1 }
;

term:
  | lvariable { $1 }
  | identifier L_PAREN term_list R_PAREN { mk_int_app $1 $3 }
  | L_PAREN term binop term R_PAREN { $3 [$2; $4] }
  | STRING_CONSTANT { mk_string_const $1 }
  | INT_CONSTANT { Z3.Arithmetic.Integer.mk_numeral_s z3_ctx $1 }
;
term_list_ne:
  | term {$1::[]}
  | term COMMA term_list_ne { $1::$3 }
;
term_list:
  | /*empty*/  {[]}
  | term_list_ne {$1}
;

formula:
  | /* empty */ { Syntax.mk_emp }
  | EMP { Syntax.mk_emp }
  | FALSE { Z3.Boolean.mk_false z3_ctx }
  | BANG identifier L_PAREN term_list R_PAREN { mk_bool_app ("!"^$2) $4 }
  | identifier L_PAREN term_list R_PAREN { mk_bool_app $1 $3 }
  | formula MULT formula { Syntax.mk_star $1 $3 }
  | formula OROR formula { Z3.Boolean.mk_or z3_ctx [$1; $3] }
  | term NOT_EQUALS term { Z3.Boolean.mk_distinct z3_ctx [$1; $3] }
  | term EQUALS term { Z3.Boolean.mk_eq z3_ctx $1 $3 }
  | term cmpop term { $2 $1 $3 }
  | qidentifier { mk_bool_var $1 } /* used for patterns */
  | L_PAREN formula R_PAREN { $2 }
;

/* Specifications */

modifies:
  | /* empty */ { [] }
  | L_PAREN lvariable_list R_PAREN { $2 }
;

/* FIXME: rubbish syntax */
in_vars:
  | /* empty */ { [] }
  | L_BRACKET lvariable_list R_BRACKET { $2 }
;

/* FIXME: rubbish syntax */
out_vars:
  | /* empty */ { [] }
  | OP_DIV lvariable_list_ne OP_DIV { $2 }
;

/* FIXME: rubbish syntax */
triple:
  | L_BRACE formula R_BRACE modifies L_BRACE out_vars formula R_BRACE in_vars
    { { Core.pre = $2; modifies = $4; post = $7; out_vars = $6; in_vars = $9 } }
;

spec:
  | /* empty */ { C.TripleSet.create 0 }
  | spec triple { C.TripleSet.add $1 $2; $1 }
  | spec OP_PLUS triple { C.TripleSet.add $1 $3; $1 }
;

/* Core statements */

assgn_lhs:
  | lvariable_list COLON_EQUALS { $1 }
  | /* empty */  { [] }
;
core_args_in: L_PAREN term_list R_PAREN { $2 };

label_list:
  | IDENTIFIER   { [$1] }
  | IDENTIFIER COMMA label_list   { $1 :: $3 }
;

call_stmt:
  | IDENTIFIER core_args_in
    { { C.call_name = $1; call_rets = []; call_args = $2 } }
  | COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $2; call_rets = []; call_args = $3 } }
  | lvariable_list_ne COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $3; call_rets = $1; call_args = $4 } }
;

core_stmt:
  | END  { C.End }
  | NOP  { C.Nop_stmt_core }
  | ASSIGN assgn_lhs spec core_args_in
    { C.Assignment_core { C.asgn_rets = $2; asgn_args = $4; asgn_spec = $3 } }
  | CALL call_stmt { C.Call_core $2 }
  | GOTO label_list { C.Goto_stmt_core $2 }
  | LABEL IDENTIFIER  { C.Label_stmt_core $2 }
;

core_stmt_list:
  | core_stmt SEMICOLON core_stmt_list  { $1 :: $3 }
  | /* empty */  { [] }
;

/* Rules */

calculus_rule:
  | RULE identifier COLON sequent
    calculus_sidecondition
    IF sequent_list SEMICOLON
    { { Calculus.schema_name = $2
      ; goal_pattern = $4
      ; subgoal_pattern = $7 } }
;

sequent:
  | formula VDASH formula
    { { Calculus.frame = Syntax.mk_emp
      ; hypothesis = $1
      ; conclusion = $3 } }
;

calculus_sidecondition:
  | /* empty for now, TODO */ { () }
;

sequent_list:
  | /* empty */ { [] }
  | sequent_list_ne { $1 }
;

sequent_list_ne:
  | sequent { [ $1 ] }
  | sequent COMMA sequent_list_ne { $1 :: $3 }
;

/* Input files */

body:
  | /* empty */ { (None, true) }
  | QUESTIONMARK core_stmt_list { (Some $2, true) }
  | BANG core_stmt_list { (Some $2, false) }
;

proc_lhs:
  | L_PAREN lvariable_list R_PAREN COLON_EQUALS { $2 }
  | /* empty */  { [] }
;

proc_args:
  | /* empty */ { [] }
  | L_PAREN lvariable_list R_PAREN { $2 }
;
procedure:
  | PROCEDURE proc_lhs identifier proc_args COLON spec body
    { { C.proc_name = $3
      ; proc_spec = $6
      ; proc_ok = snd $7
      ; proc_body = fst $7
      ; proc_params = $4
      ; proc_rets = $2
      ; proc_rules = { C.calculus = []; abstraction = [] } } }
;

import_entry:
  | IMPORT STRING_CONSTANT SEMICOLON  { $2 }
;

normal_entry:
  | procedure { ParserAst.Procedure $1 }
  | GLOBAL identifier_list_ne SEMICOLON { ParserAst.Global $2 }
  | calculus_rule { ParserAst.CalculusRule $1 }
;

entry:
  | import_entry { Load.ImportEntry $1 }
  | normal_entry { Load.NormalEntry $1 }
;

entry_list:
  | /* empty */ { [] }
  | entry entry_list { $1 :: $2 }
;

file:
  | entry_list EOF { $1 }
;

%% (* trailer *)
