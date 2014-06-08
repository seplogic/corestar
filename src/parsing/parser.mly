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

let mk_int_app op args =
  let fdecl = Z3.FuncDecl.mk_func_decl_s z3_ctx op
    (List.map (fun _ -> int_sort) args) int_sort in
  Z3.Expr.mk_app z3_ctx fdecl args
let mk_bool_app op args =
  let fdecl = Z3.FuncDecl.mk_func_decl_s z3_ctx op
    (List.map (fun _ -> int_sort) args) bool_sort in
  Z3.Expr.mk_app z3_ctx fdecl args

let mk_string_const = Syntax.mk_string_const

%} /* declarations */

/* ============================================================= */
/* tokens */
%token ABDUCT
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
%token FRESH
%token GLOBAL
%token GOTO
%token IDENTIFIER
%token IF
%token IMPORT
%token IN
%token INCONSISTENT
%token INT_CONSTANT
%token L_BRACE
%token L_BRACKET
%token L_PAREN
%token LABEL
%token LEFTARROW
%token LIDENTIFIER
%token MULT
%token NOP
%token NO_BACKTRACK
%token NOT_EQUALS
%token OP_DIV
%token OP_MINUS
%token OP_PLUS
%token OROR
%token PGIDENTIFIER
%token PLIDENTIFIER
%token PROCEDURE
%token PUREIDENTIFIER
%token PURECHECK
%token R_BRACE
%token R_BRACKET
%token R_PAREN
%token RETURNS
%token RULE
%token SEMICOLON
%token SPEC
%token STRING_CONSTANT
%token TPIDENTIFIER
%token VDASH
%token VPIDENTIFIER

/* types */
%type <string> IDENTIFIER
%type <string> INT_CONSTANT
%type <string> PGIDENTIFIER
%type <string> PLIDENTIFIER
%type <string> PUREIDENTIFIER
%type <string> LIDENTIFIER
%type <string> STRING_CONSTANT
%type <string> TPIDENTIFIER
%type <string> VPIDENTIFIER

/* associativity and precedence */

%left OROR
%left OP_PLUS
%left OP_MINUS
%left MULT

/* entry point */
%start file
%type <ParserAst.entry Load.entry list> file

%% /* rules */

/* Identifiers and constants */

cmpop:
  | CMP_LE { Z3.Arithmetic.mk_le z3_ctx }
  | CMP_LT { Z3.Arithmetic.mk_lt z3_ctx }
  | CMP_GE { Z3.Arithmetic.mk_ge z3_ctx }
  | CMP_GT { Z3.Arithmetic.mk_gt z3_ctx }
;


/* Expressions */

variable:
  | PGIDENTIFIER { Syntax.mk_int_pgvar $1 }
  | PLIDENTIFIER { Syntax.mk_int_plvar $1 }
  | LIDENTIFIER { Syntax.mk_int_lvar $1 }
  | TPIDENTIFIER { Syntax.mk_int_tpat $1 }
  | VPIDENTIFIER { Syntax.mk_int_vpat $1 }
;
variable_list_ne:
  |  variable    { [$1] }
  |  variable COMMA variable_list_ne  { $1 :: $3 }
;
variable_list:
  |  {[]}
  | variable_list_ne { $1 }
;

term:
  | function_ { mk_int_app (fst $1) (snd $1) }
  | variable { $1 }
  | term_nf { $1 }
  | L_PAREN term_nf R_PAREN { $2 }
;

term_nf:
  | STRING_CONSTANT { mk_string_const $1 }
  | INT_CONSTANT { Z3.Arithmetic.Integer.mk_numeral_s z3_ctx $1 }
  | term OP_MINUS term { Z3.Arithmetic.mk_sub z3_ctx [$1; $3] }
  | term OP_PLUS term { Z3.Arithmetic.mk_add z3_ctx [$1; $3] }
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
  | function_ { mk_bool_app (fst $1) (snd $1) }
  | TPIDENTIFIER { Syntax.mk_bool_tpat $1 } /* used for patterns */
  | formula_nf { $1 }
  | L_PAREN formula_nf R_PAREN { $2 }
;

formula_nf:
  | /* empty */ { Syntax.mk_emp }
  | EMP { Syntax.mk_emp }
  | FALSE { Z3.Boolean.mk_false z3_ctx }
  | PUREIDENTIFIER L_PAREN term_list R_PAREN { mk_bool_app ("!"^$1) $3 }
  | formula MULT formula { Syntax.mk_star $1 $3 }
  | formula OROR formula { Z3.Boolean.mk_or z3_ctx [$1; $3] }
  | term NOT_EQUALS term { Syntax.mk_distinct [$1; $3] }
  | term EQUALS term { Syntax.mk_eq $1 $3 }
  | term cmpop term { $2 $1 $3 }
;

function_:
  | IDENTIFIER L_PAREN term_list R_PAREN { ($1, $3) }
  | L_PAREN function_ R_PAREN { $2 }
;

/* Specifications */

modifies:
  | /* empty */ { [] }
  | L_PAREN variable_list R_PAREN { $2 }
;

triple:
  | L_BRACE formula R_BRACE modifies L_BRACE formula R_BRACE
    { { Core.pre = $2; modifies = $4; post = $6 } }
;

spec:
  | /* empty */ { C.TripleSet.create 0 }
  | spec triple { C.TripleSet.add $1 $2; $1 }
  | spec OP_PLUS triple { C.TripleSet.add $1 $3; $1 }
;

/* Core statements */

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
  | variable_list_ne COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $3; call_rets = $1; call_args = $4 } }
;

spec_subst_ne:
  | L_BRACKET variable_list LEFTARROW term_list R_BRACKET { ($2, $4) }
;

spec_subst:
  | /* empty */ { ([], []) }
  | spec_subst_ne { $1 }
;

spec_subst_ret:
  | /* empty */ { ([], []) }
  | RETURNS spec_subst_ne { $2 }
;

core_stmt:
  | END  { C.End }
  | NOP  { C.Nop_stmt_core }
  | SPEC spec spec_subst spec_subst_ret
    { C.Assignment_core
      { C.asgn_rets = snd $4
      ; asgn_rets_formal = fst $4
      ; asgn_args = snd $3
      ; asgn_args_formal = fst $3
      ; asgn_spec = $2 } }
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
  | RULE rule_flags IDENTIFIER rule_priority COLON sequent
    sidecondition_list
    IF sequent_list SEMICOLON
    { { Calculus.seq_name = $3
      ; seq_pure_check = fst $7
      ; seq_fresh_in_expr = snd $7
      ; seq_goal_pattern = $6
      ; seq_subgoal_pattern = $9
      ; seq_priority = $4
      ; seq_flags = $2 } }
;

rule_flag:
  | NO_BACKTRACK { Calculus.rule_no_backtrack }
  | ABDUCT { Calculus.rule_abduct }
  | INCONSISTENT { Calculus.rule_inconsistency }
;
rule_flags:
  | /* empty */ { 0 }
  | rule_flag rule_flags { $1 lor $2 }
;

rule_priority:
  | /* empty */ { Calculus.default_rule_priority }
  | L_PAREN INT_CONSTANT R_PAREN { int_of_string $2 }
;

sidecondition:
  | PURECHECK term { (Some $2, None) }
  | FRESH variable IN term { (None,  Some ($2,$4)) }
;
sidecondition_list_ne:
  | sidecondition { (option [] (fun x -> [x]) (fst $1),
		     option [] (fun x -> [x]) (snd $1)) }
  | sidecondition SEMICOLON sidecondition_list_ne
      { (option (fst $3) (flip ListH.cons (fst $3)) (fst $1),
	 option (snd $3) (flip ListH.cons (snd $3)) (snd $1)) }
;
sidecondition_list:
  | /*empty*/  { ([], []) }
  | sidecondition_list_ne { $1 }
;

sequent:
  | formula VDASH formula
    { { Calculus.frame = Syntax.mk_emp
      ; hypothesis = $1
      ; conclusion = $3 } }
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
  | COLON core_stmt_list { (Some $2, true) }
  | BANG core_stmt_list { (Some $2, false) }
;

proc_args:
  | /* empty */ { [] }
  | L_PAREN variable_list R_PAREN { $2 }
;

proc_rets:
  | /* empty */ { [] }
  | RETURNS L_PAREN variable_list R_PAREN { $3 }

procedure:
  | PROCEDURE IDENTIFIER proc_args proc_rets spec body
    { { C.proc_name = $2
      ; proc_spec = $5
      ; proc_ok = snd $6
      ; proc_body = fst $6
      ; proc_args = $3
      ; proc_rets = $4
      ; proc_rules = { C.calculus = []; abstraction = [] } } }
;

import_entry:
  | IMPORT STRING_CONSTANT SEMICOLON  { $2 }
;

normal_entry:
  | procedure { ParserAst.Procedure $1 }
  | calculus_rule { ParserAst.CalculusRule (Calculus.Sequent_rule $1) }
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
