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
exception Give_up

open Core
open Lexing
open Parsing
open Printing
open Psyntax
open Spec
open Vars

let newVar x =
  if x.[0] = '_' then begin
    let x = String.sub x 1 (String.length x - 1) in
    if x = "" then Vars.freshe () else Vars.concretee_str x
  end else Vars.concretep_str x

let file_name = ref None

let location_to_string pos =
  Printf.sprintf "Line %d character %d" pos.pos_lnum  (pos.pos_cnum - pos.pos_bol + 1)

let parse_error s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Error between %s and %s\n%s\n" (location_to_string start_pos) (location_to_string end_pos) s

let parse_warning s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Warning %s (between %s and %s)\n" s (location_to_string start_pos) (location_to_string end_pos)


%} /* declarations */

/* ============================================================= */
/* tokens */
%token ABDUCTION
%token ABSRULE
%token ABSTRACT
%token AND
%token ASSIGN
%token AXIOMS
%token BANG
%token BIMP
%token CALL
%token CMP_LE
%token CMP_LT
%token CMP_GE
%token CMP_GT
%token COLON
%token COLON_EQUALS
%token COMMA
%token CONSTRUCTOR
%token DASHV
%token DOT
%token EMP
%token END
%token EOF
%token EQUALS
%token EQUIV
%token FALSE
%token FRAME
%token GARBAGE
%token GOTO
%token <string> IDENTIFIER
%token IF
%token IMP
%token IMPLICATION
%token IMPORT
%token INCONSISTENCY
%token LABEL
%token L_BRACE
%token L_BRACKET
%token L_PAREN
%token LEADSTO
%token MULT
%token NOP
%token NOT_EQUALS
%token NOTIN
%token NOTINCONTEXT
%token PUREGUARD
%token OP_DIV
%token OP_MINUS
%token OP_PLUS
%token OR
%token OROR
%token ORTEXT
%token QUESTIONMARK
%token QUOTE
%token R_BRACE
%token R_BRACKET
%token R_PAREN
%token REWRITERULE
%token RULE
%token SEMICOLON
%token SPECIFICATION
%token SPECTEST
%token <string> STRING_CONSTANT
%token TRUE
%token VDASH
%token WAND
%token WHERE
%token WITH
%token WITHOUT

/* === associativity and precedence === */

%left IDENTIFIER
%left AT_IDENTIFIER
%left OR
%left OROR
%left MULT

/* entry points */
%start rule_file
%type <Psyntax.rules Load.importoption list> rule_file

%start question_file
%type <Psyntax.question list> question_file

%start test_file
%type <Psyntax.test list> test_file

%start symb_question_file
%type <Core.ast_spec Core.symb_question list> symb_question_file

%start symb_test_file
%type <Core.ast_spec Core.symb_test list> symb_test_file

%% /* rules */

/* Identifiers and constants */

boolean:
  | TRUE { true }
  | FALSE { false }
;

identifier:
  | IDENTIFIER { $1 }
;

identifier_op:
  | /* empty */ {""}
  | identifier  {$1}
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

lvariable:
  | identifier { newVar($1) }
  | QUESTIONMARK identifier { Vars.concretea_str $2 }
;
lvariable_list_ne:
  |  lvariable    { [$1] }
  |  lvariable COMMA lvariable_list_ne  { $1 :: $3 }
;
lvariable_list:
  |  {[]}
  | lvariable_list_ne { $1 }
;

lvariable_npv:
  | identifier { newVar($1) }
;
lvariable_npv_list_ne:
  |  lvariable_npv    { [$1] }
  |  lvariable_npv COMMA lvariable_npv_list_ne  { $1 :: $3 }
;
lvariable_npv_list:
  |  {[]}
  | lvariable_npv_list_ne { $1 }
;

/* Code for matching where not allowing question mark variables:
   no pattern vars */
term_npv:
  | lvariable_npv {Arg_var ($1)}
  | identifier L_PAREN term_npv_list R_PAREN { Arg_op($1, $3) }
  | L_PAREN term_npv binop term_npv R_PAREN { Arg_op($3, [$2;$4]) }
  | L_BRACE fldlist_npv R_BRACE { mkArgRecord $2 }
  | STRING_CONSTANT { Arg_string($1) }
;
term_npv_list_ne:
  | term_npv {$1::[]}
  | term_npv COMMA term_npv_list_ne { $1::$3 }
;
term_npv_list:
  | /*empty*/  {[]}
  | term_npv_list_ne {$1}
;

/* With pattern vars*/
term:
  | lvariable { Arg_var ($1) }
  | identifier L_PAREN term_list R_PAREN { Arg_op($1, $3) }
  | L_PAREN term binop term R_PAREN { Arg_op($3, [$2;$4]) }
  | L_BRACE fldlist R_BRACE { mkArgRecord $2 }
  | STRING_CONSTANT { Arg_string($1) }
;
term_list_ne:
  | term {$1::[]}
  | term COMMA term_list_ne { $1::$3 }
;
term_list:
  | /*empty*/  {[]}
  | term_list_ne {$1}
;

fldlist_npv:
   | identifier EQUALS term_npv { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS term_npv SEMICOLON fldlist_npv  { ($1,$3) :: $5 }
;

fldlist:
   | identifier EQUALS term { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS term SEMICOLON fldlist  { ($1,$3) :: $5 }
;


/* Formulae */

formula:
  | /*empty*/  { mkEmpty }
  | EMP  { mkEmpty }
  | FALSE { mkFalse}
  | BANG identifier L_PAREN term_list R_PAREN { mkPPred ($2, $4) }
  | identifier L_PAREN term_list R_PAREN { mkSPred($1,$3) }
  | formula MULT formula { mkStar $1 $3 }
  | formula OROR formula { mkOr ($1,$3) }
  | term NOT_EQUALS term { mkNEQ ($1,$3) }
  | term EQUALS term { mkEQ ($1, $3) }
  | term cmpop term { mkPPred ($2, [$1;$3]) }
  | L_PAREN formula R_PAREN { $2 }
;

formula_npv:
  | /*empty*/  { mkEmpty }
  | EMP  { mkEmpty }
  | FALSE { mkFalse}
  | BANG identifier L_PAREN term_npv_list R_PAREN { mkPPred ($2, $4) }
  | identifier L_PAREN term_npv_list R_PAREN { mkSPred($1,$3) }
  | formula_npv MULT formula_npv { mkStar $1 $3 }
  | formula_npv OROR formula_npv { mkOr ($1,$3) }
  | term_npv NOT_EQUALS term_npv { mkNEQ ($1,$3) }
  | term_npv EQUALS term_npv { mkEQ ($1,$3) }
  | term_npv cmpop term_npv { mkPPred ($2, [$1;$3]) }
  | L_PAREN formula_npv R_PAREN { $2 }
;

spatial_at:
  | identifier L_PAREN term_list R_PAREN { mkSPred($1,$3) }
;
spatial_list_ne:
  | spatial_at MULT spatial_list_ne  { mkStar $1 $3 }
  | spatial_at    { $1 }
;
spatial_list:
  | spatial_list_ne { $1 }
  | /*empty*/  { mkEmpty }
;


/* Sequents and rules */

sequent:
  | spatial_list OR formula VDASH formula { ($1,$3,$5,mkEmpty) }
  | spatial_list OR formula VDASH formula DASHV formula { ($1,$3,$5,$7) }
;
sequent_list:
  |  /* empty */ { [] }
  | TRUE { [] }
  | sequent {[$1]}
  | sequent SEMICOLON sequent_list { $1::$3 }
;
sequent_list_or_list:
  |  sequent_list {[$1]}
  |  sequent_list ORTEXT sequent_list_or_list { $1::$3 }
;

without:
  | WITHOUT formula { ($2, mkEmpty) }
  | WITHOUT formula VDASH formula { ($2,$4) }
  | /* empty */ { (mkEmpty,mkEmpty) }
;

without_simp:
  | WITHOUT formula { $2 }
  | /* empty */ { [] }
;

varterm:
  | lvariable_list { Var(vs_from_list $1) }
;

clause:
  | varterm NOTINCONTEXT { NotInContext($1) }
  | varterm NOTIN term { NotInTerm($1,$3) }
  | formula PUREGUARD { PureGuard($1) }   /* TODO: check that the formula here is really pure */
;

clause_list:
  | clause  { [$1] }
  | clause SEMICOLON clause_list {$1 :: $3}
;

where:
  | WHERE clause_list { $2 }
  | /* empty */ { [] }
;

ifclause:
  | /* empty plain term */ { [] }
  | IF formula {$2}
;

/* Need to do tests that simplified rules are fine for pure bits.*/
equiv_rule:
  | EQUIV identifier_op COLON formula IMP formula BIMP formula without_simp  { EquivRule($2,$4,$6,$8,$9) }
  | EQUIV identifier_op COLON formula IMP formula without_simp  { EquivRule($2,$4,$6,mkEmpty,$7) }
  | EQUIV identifier_op COLON formula BIMP formula without_simp  { EquivRule($2,mkEmpty,$4,$6,$7) }
;

rule:
  | CONSTRUCTOR identifier  { Load.NormalEntry( ConsDecl($2) ) }
  | IMPORT STRING_CONSTANT SEMICOLON  { Load.ImportEntry($2) }
  | RULE identifier_op COLON sequent without where IF sequent_list_or_list
    { Load.NormalEntry(SeqRule($4,$8,$2,$5,$6)) }
  | REWRITERULE identifier_op COLON identifier L_PAREN term_list R_PAREN EQUALS term ifclause without_simp where
    { Load.NormalEntry(RewriteRule({function_name=$4;
        arguments=$6;
        result=$9;
        guard={without_form=$11;rewrite_where=$12;if_form=$10};
        rewrite_name=$2;
        saturate=false})) }
  | REWRITERULE identifier_op MULT COLON identifier L_PAREN term_list R_PAREN EQUALS term ifclause without_simp where
    { Load.NormalEntry(RewriteRule({function_name=$5;
        arguments=$7;
        result=$10;
        guard={without_form=$12; rewrite_where=$13; if_form=$11};
        rewrite_name=$2;
        saturate=true})) }
  | ABSRULE identifier_op COLON formula LEADSTO formula where  { let seq=(mkEmpty,$4,mkEmpty,mkEmpty) in
      let wo=(mkEmpty,mkEmpty) in
      let seq2=(mkEmpty,$6,mkEmpty,mkEmpty) in
      let seq_list=[[seq2]] in
      Load.NormalEntry(SeqRule(seq,seq_list,$2,wo,$7)) }
  | equiv_rule { Load.NormalEntry($1) }
;

rule_file:
  | EOF  { [] }
  | rule rule_file  { $1 :: $2 }
;


/* Specifications */

triple:
  L_BRACE formula R_BRACE L_BRACE formula R_BRACE
    { { Spec.pre = $2; post = $5 } }
;

spec:
  | /* empty */ { HashSet.create 1 }
  | spec triple { HashSet.add $1 $2; $1 }
;


/* Core statements */

core_assn_args:
  | lvariable_npv_list COLON_EQUALS { $1 }
  | /* empty */  { [] }
;
core_args_in: L_PAREN term_npv_list R_PAREN { $2 };

label_list:
  | IDENTIFIER   { [$1] }
  | IDENTIFIER COMMA label_list   { $1 :: $3 }
;

call_stmt: /* split in cases to avoid parsing conflict */
  | IDENTIFIER core_args_in
    { { call_name = $1; call_rets = []; call_args = $2 } }
  | lvariable_npv COLON_EQUALS IDENTIFIER core_args_in
    { { call_name = $3; call_rets = [$1]; call_args = $4 } }
  | lvariable_npv COMMA lvariable_npv_list_ne COLON_EQUALS IDENTIFIER core_args_in
    { { call_name = $5; call_rets = $1 :: $3; call_args = $6 } }
;

core_stmt:
  | END  { End }
  | NOP  { Nop_stmt_core }
  | ASSIGN core_assn_args spec core_args_in
    { Assignment_core { asgn_rets = $2; asgn_args = $4; asgn_spec = $3 } }
  | CALL call_stmt { Call_core $2 }
  | GOTO label_list { Goto_stmt_core $2 }
  | LABEL IDENTIFIER  { Label_stmt_core $2 }
;

core_stmt_list:
  | core_stmt SEMICOLON core_stmt_list  { $1 :: $3 }
  | /* empty */  { [] }
;


/* Input files */

question:
  | IMPLICATION COLON formula_npv VDASH formula_npv {Implication($3,$5)}
  | INCONSISTENCY COLON formula_npv {Inconsistency($3)}
  | FRAME COLON formula_npv VDASH formula_npv {Frame($3,$5)}
  | ABDUCTION COLON formula_npv VDASH formula_npv {Abduction($3,$5)}
;

test:
  | IMPLICATION COLON formula_npv VDASH formula_npv QUESTIONMARK boolean { TImplication($3,$5,$7) }
  | INCONSISTENCY COLON formula_npv QUESTIONMARK boolean { TInconsistency($3,$5) }
  | FRAME COLON formula_npv VDASH formula_npv QUESTIONMARK formula_npv { TFrame($3,$5,$7) }
;

question_file:
  | EOF  { [] }
  | question question_file  {$1 :: $2}
;

test_file:
  | EOF  { [] }
  | test test_file  { $1 :: $2 }
;

symb_question:
  | SPECIFICATION identifier COLON spec QUESTIONMARK core_stmt_list
    { {proc_name=$2; proc_spec=$4; proc_body=Some $6} }
  | SPECIFICATION identifier COLON spec
    { {proc_name=$2; proc_spec=$4; proc_body=None} }
;

symb_test:
  | SPECTEST identifier COLON spec QUESTIONMARK boolean core_stmt_list
    {({proc_name=$2; proc_spec=$4; proc_body=Some $7}, $6)}
;

symb_question_file:
  | EOF  { [] }
  | symb_question symb_question_file  {$1 :: $2}
;

symb_test_file:
  | EOF  { [] }
  | symb_test symb_test_file  {$1 :: $2}
;

%% (* trailer *)
