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
module Expr = Expression

let newVar x =
  if x.[0] = '_' then begin
    let x = String.sub x 1 (String.length x - 1) in
    if x = "" then Vars.freshe () else Vars.concretee_str x
  end else Vars.concretep_str x

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
%token EMP
%token END
%token EOF
%token EQUALS
%token FALSE
%token GLOBAL
%token GOTO
%token IDENTIFIER
%token IMPORT
%token LABEL
%token L_BRACE
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
%token R_BRACE
%token R_PAREN
%token SEMICOLON
%token STRING_CONSTANT

/* types */
%type <string> IDENTIFIER
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

binop:
  | OP_DIV { "builtin_div" }
  | OP_MINUS { "builtin_minus" }
  | OP_PLUS { "builtin_plus" }
;

cmpop:
  | CMP_LE { "builtin_le" }
  | CMP_LT { "builtin_lt" }
  | CMP_GE { "builtin_ge" }
  | CMP_GT { "builtin_gt" }
;


/* Expressions */

identifier_list_ne:
  | identifier { [ $1 ] }
  | identifier COMMA identifier_list_ne { $1 :: $3 }
;

lvariable:
  | identifier { $1 }
  | QUESTIONMARK identifier { "?" ^ $2 }
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
  | lvariable { Expr.mk_var $1 }
  | identifier L_PAREN term_list R_PAREN { Expr.mk_app $1 $3 }
  | L_PAREN term binop term R_PAREN { Expr.mk_app $3 [$2; $4] }
  | STRING_CONSTANT { Expr.mk_string_const $1 }
;
term_list_ne:
  | term {$1::[]}
  | term COMMA term_list_ne { $1::$3 }
;
term_list:
  | /*empty*/  {[]}
  | term_list_ne {$1}
;

/* Formulae */

formula:
  | /*empty*/  { Expr.emp }
  | EMP  { Expr.emp }
  | FALSE { Expr.fls }
  | BANG identifier L_PAREN term_list R_PAREN { Expr.mk_app ("!"^$2) $4 }
  | identifier L_PAREN term_list R_PAREN { Expr.mk_app $1 $3 }
  | formula MULT formula { Expr.mk_2 "*" $1 $3 }
  | formula OROR formula { Expr.mk_2 "or" $1 $3 }
  | term NOT_EQUALS term { Expr.mk_2 "!=" $1 $3 }
  | term EQUALS term { Expr.mk_2 "==" $1 $3 }
  | term cmpop term { Expr.mk_2 $2 $1 $3 }
  | L_PAREN formula R_PAREN { $2 }
;

/* Specifications */

triple:
  L_BRACE formula R_BRACE L_BRACE formula R_BRACE
    { { Core.pre = $2; post = $5; modifies = None } }
;

spec:
  | /* empty */ { C.TripleSet.create 0 }
  | spec triple { C.TripleSet.add $1 $2; $1 }
;


/* Core statements */

core_assn_args:
  | lvariable_list COLON_EQUALS { $1 }
  | /* empty */  { [] }
;
core_args_in: L_PAREN term_list R_PAREN { $2 };

label_list:
  | IDENTIFIER   { [$1] }
  | IDENTIFIER COMMA label_list   { $1 :: $3 }
;

call_stmt: /* split in cases to avoid parsing conflict */
  | IDENTIFIER core_args_in
    { { C.call_name = $1; call_rets = []; call_args = $2 } }
  | lvariable COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $3; call_rets = [$1]; call_args = $4 } }
  | lvariable COMMA lvariable_list_ne COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $5; call_rets = $1 :: $3; call_args = $6 } }
;

core_stmt:
  | END  { C.End }
  | NOP  { C.Nop_stmt_core }
  | ASSIGN core_assn_args spec core_args_in
    { C.Assignment_core { C.asgn_rets = $2; asgn_args = $4; asgn_spec = $3 } }
  | CALL call_stmt { C.Call_core $2 }
  | GOTO label_list { C.Goto_stmt_core $2 }
  | LABEL IDENTIFIER  { C.Label_stmt_core $2 }
;

core_stmt_list:
  | core_stmt SEMICOLON core_stmt_list  { $1 :: $3 }
  | /* empty */  { [] }
;


/* Input files */

body:
  | /* empty */ { (None, true) }
  | QUESTIONMARK core_stmt_list { (Some $2, true) }
  | BANG core_stmt_list { (Some $2, false) }
;

procedure:
  | PROCEDURE identifier COLON spec body
    { { C.proc_name = $2
      ; proc_spec = $4
      ; proc_ok = snd $5
      ; proc_body = fst $5
      ; proc_rules = { C.calculus = []; abstraction = [] } } }
;

import_entry:
  | IMPORT STRING_CONSTANT SEMICOLON  { $2 }
;

normal_entry:
  | procedure { ParserAst.Procedure $1 }
  | GLOBAL identifier_list_ne SEMICOLON { ParserAst.Global $2 }
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
