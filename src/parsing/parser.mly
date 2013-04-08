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

(* TODO(rgrig): Don't open these. *)
open Lexing
open Parsing
open Printing
open Vars

module C = Core
module PS = Psyntax

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
%token <string> IDENTIFIER
%token <string> STRING_CONSTANT
%token ABDUCTION
%token ABSRULE
%token ABSTRACT
%token AND
%token ASSIGN
%token AXIOMS
%token BANG
%token BIMP
%token CALL
%token CMP_GE
%token CMP_GT
%token CMP_LE
%token CMP_LT
%token COLON
%token COLON_EQUALS
%token COMMA
%token CONSTRUCTOR
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
%token IF
%token IMP
%token IMPLICATION
%token IMPORT
%token INCONSISTENCY
%token LABEL
%token LEADSTO
%token L_BRACE
%token L_BRACKET
%token L_PAREN
%token MULT
%token NOP
%token NOTIN
%token NOTINCONTEXT
%token NOT_EQUALS
%token OP_DIV
%token OP_MINUS
%token OP_PLUS
%token OR
%token OROR
%token ORTEXT
%token PROCEDURE
%token PUREGUARD
%token QUESTIONMARK
%token QUOTE
%token REWRITERULE
%token RULE
%token R_BRACE
%token R_BRACKET
%token R_PAREN
%token SEMICOLON
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

/* entry point */
%start file
%type <ParserAst.entry Load.entry list> file

%% /* rules */

/* Identifiers and constants */

identifier:
  | IDENTIFIER { $1 }
;

identifier_op:
  | /* empty */ {""} /* TODO(rgrig): fresh name, mentioning the location */
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
  | lvariable_npv { PS.Arg_var ($1)}
  | identifier L_PAREN term_npv_list R_PAREN { PS.Arg_op($1, $3) }
  | L_PAREN term_npv binop term_npv R_PAREN { PS.Arg_op($3, [$2;$4]) }
  | L_BRACE fldlist_npv R_BRACE { PS.mkArgRecord $2 }
  | STRING_CONSTANT { PS.Arg_string($1) }
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
  | lvariable { PS.Arg_var ($1) }
  | identifier L_PAREN term_list R_PAREN { PS.Arg_op($1, $3) }
  | L_PAREN term binop term R_PAREN { PS.Arg_op($3, [$2;$4]) }
  | L_BRACE fldlist R_BRACE { PS.mkArgRecord $2 }
  | STRING_CONSTANT { PS.Arg_string($1) }
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
  | /*empty*/  { PS.mkEmpty }
  | EMP  { PS.mkEmpty }
  | FALSE { PS.mkFalse }
  | BANG identifier L_PAREN term_list R_PAREN { PS.mkPPred ($2, $4) }
  | identifier L_PAREN term_list R_PAREN { PS.mkSPred($1,$3) }
  | formula MULT formula { PS.mkStar $1 $3 }
  | formula OROR formula { PS.mkOr ($1,$3) }
  | term NOT_EQUALS term { PS.mkNEQ ($1,$3) }
  | term EQUALS term { PS.mkEQ ($1, $3) }
  | term cmpop term { PS.mkPPred ($2, [$1;$3]) }
  | L_PAREN formula R_PAREN { $2 }
;

formula_npv:
  | /*empty*/  { PS.mkEmpty }
  | EMP  { PS.mkEmpty }
  | FALSE { PS.mkFalse}
  | BANG identifier L_PAREN term_npv_list R_PAREN { PS.mkPPred ($2, $4) }
  | identifier L_PAREN term_npv_list R_PAREN { PS.mkSPred($1,$3) }
  | formula_npv MULT formula_npv { PS.mkStar $1 $3 }
  | formula_npv OROR formula_npv { PS.mkOr ($1,$3) }
  | term_npv NOT_EQUALS term_npv { PS.mkNEQ ($1,$3) }
  | term_npv EQUALS term_npv { PS.mkEQ ($1,$3) }
  | term_npv cmpop term_npv { PS.mkPPred ($2, [$1;$3]) }
  | L_PAREN formula_npv R_PAREN { $2 }
;

spatial_at:
  | identifier L_PAREN term_list R_PAREN { PS.mkSPred($1,$3) }
;
spatial_list_ne:
  | spatial_at MULT spatial_list_ne  { PS.mkStar $1 $3 }
  | spatial_at    { $1 }
;
spatial_list:
  | spatial_list_ne { $1 }
  | /*empty*/  { PS.mkEmpty }
;


/* Sequents and rules */

sequent:
    spatial_list OR formula VDASH formula { PS.mk_psequent $1 $3 $5 }
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
  | WITHOUT formula { ($2, PS.mkEmpty) }
  | WITHOUT formula VDASH formula { ($2,$4) }
  | /* empty */ { (PS.mkEmpty, PS.mkEmpty) }
;

without_simp:
  | WITHOUT formula { $2 }
  | /* empty */ { [] }
;

varterm:
  | lvariable_list { PS.Var (PS.vs_from_list $1) }
;

clause:
  | varterm NOTINCONTEXT { PS.NotInContext $1 }
  | varterm NOTIN term { PS.NotInTerm ($1,$3) }
  | formula PUREGUARD { PS.PureGuard $1 }   /* TODO: check that the formula here is really pure */
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

/* TODO: Test that simplified rules are fine for pure bits.*/
equiv_rule:
  | EQUIV identifier_op COLON formula IMP formula BIMP formula without_simp
    { PS.EquivRule ($2,$4,$6,$8,$9) }
  | EQUIV identifier_op COLON formula IMP formula without_simp
    { PS.EquivRule ($2,$4,$6,PS.mkEmpty,$7) }
  | EQUIV identifier_op COLON formula BIMP formula without_simp
    { PS.EquivRule ($2,PS.mkEmpty,$4,$6,$7) }
;

rule:
  | CONSTRUCTOR identifier
    { PS.ConsDecl $2 }
  | RULE identifier_op COLON sequent without where IF sequent_list_or_list
    { PS.SeqRule($4,$8,$2,$5,$6) }
  | REWRITERULE identifier_op COLON identifier L_PAREN term_list R_PAREN EQUALS term ifclause without_simp where
    { PS.RewriteRule
      ( { PS.function_name = $4
        ; arguments = $6
        ; result = $9
        ; guard = { PS.without_form=$11; rewrite_where=$12; if_form=$10 }
        ; rewrite_name = $2
        ; saturate = false } ) }
  | REWRITERULE identifier_op MULT COLON identifier L_PAREN term_list R_PAREN EQUALS term ifclause without_simp where
    { PS.RewriteRule
      ( { PS.function_name = $5
        ; arguments = $7
        ; result = $10
        ; guard = { PS.without_form=$12; rewrite_where=$13; if_form=$11 }
        ; rewrite_name = $2
        ; saturate=true } ) }
  | ABSRULE identifier_op COLON formula LEADSTO formula where
    { let seq = PS.mk_psequent PS.mkEmpty $4 PS.mkEmpty in
      let wo = (PS.mkEmpty, PS.mkEmpty) in
      let seq2= PS.mk_psequent PS.mkEmpty $6 PS.mkEmpty in
      let seq_list=[[seq2]] in
      PS.SeqRule(seq,seq_list,$2,wo,$7) }
  | equiv_rule { $1 }
;

/* Specifications */

triple:
  L_BRACE formula R_BRACE L_BRACE formula R_BRACE
    { { Core.pre = $2; post = $5 } }
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
    { { C.call_name = $1; call_rets = []; call_args = $2 } }
  | lvariable_npv COLON_EQUALS IDENTIFIER core_args_in
    { { C.call_name = $3; call_rets = [$1]; call_args = $4 } }
  | lvariable_npv COMMA lvariable_npv_list_ne COLON_EQUALS IDENTIFIER core_args_in
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

prover_query:
  | IMPLICATION COLON formula_npv VDASH formula_npv {PS.Implication($3,$5)}
  | INCONSISTENCY COLON formula_npv {PS.Inconsistency($3)}
  | FRAME COLON formula_npv VDASH formula_npv {PS.Frame($3,$5)}
  | ABDUCTION COLON formula_npv VDASH formula_npv {PS.Abduction($3,$5)}
;

body:
  | /* empty */ { None }
  | QUESTIONMARK core_stmt_list { Some $2 }
;

procedure:
  | PROCEDURE identifier COLON spec body
    { { C.proc_name = $2
      ; proc_spec = $4
      ; proc_body = $5
      ; proc_rules = Psyntax.empty_logic (* XXX *) } }
;

import_entry:
  | IMPORT STRING_CONSTANT SEMICOLON  { $2 }
;

normal_entry:
  | procedure { ParserAst.Procedure $1 }
  | prover_query { ParserAst.ProverQuery $1 }
  | rule { ParserAst.Rule $1 }
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
