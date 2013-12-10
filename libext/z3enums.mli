(* Automatically generated file *)

(** The enumeration types of Z3. *)

(** lbool *)
type lbool =
  | L_TRUE 
  | L_UNDEF 
  | L_FALSE 

(** Convert lbool to int*)
val int_of_lbool : lbool -> int
(** Convert int to lbool*)
val lbool_of_int : int -> lbool

(** symbol_kind *)
type symbol_kind =
  | INT_SYMBOL 
  | STRING_SYMBOL 

(** Convert symbol_kind to int*)
val int_of_symbol_kind : symbol_kind -> int
(** Convert int to symbol_kind*)
val symbol_kind_of_int : int -> symbol_kind

(** parameter_kind *)
type parameter_kind =
  | PARAMETER_FUNC_DECL 
  | PARAMETER_DOUBLE 
  | PARAMETER_SYMBOL 
  | PARAMETER_INT 
  | PARAMETER_AST 
  | PARAMETER_SORT 
  | PARAMETER_RATIONAL 

(** Convert parameter_kind to int*)
val int_of_parameter_kind : parameter_kind -> int
(** Convert int to parameter_kind*)
val parameter_kind_of_int : int -> parameter_kind

(** sort_kind *)
type sort_kind =
  | BV_SORT 
  | FINITE_DOMAIN_SORT 
  | ARRAY_SORT 
  | UNKNOWN_SORT 
  | RELATION_SORT 
  | REAL_SORT 
  | INT_SORT 
  | UNINTERPRETED_SORT 
  | BOOL_SORT 
  | DATATYPE_SORT 

(** Convert sort_kind to int*)
val int_of_sort_kind : sort_kind -> int
(** Convert int to sort_kind*)
val sort_kind_of_int : int -> sort_kind

(** ast_kind *)
type ast_kind =
  | VAR_AST 
  | SORT_AST 
  | QUANTIFIER_AST 
  | UNKNOWN_AST 
  | FUNC_DECL_AST 
  | NUMERAL_AST 
  | APP_AST 

(** Convert ast_kind to int*)
val int_of_ast_kind : ast_kind -> int
(** Convert int to ast_kind*)
val ast_kind_of_int : int -> ast_kind

(** decl_kind *)
type decl_kind =
  | OP_LABEL 
  | OP_PR_REWRITE 
  | OP_UNINTERPRETED 
  | OP_SUB 
  | OP_ZERO_EXT 
  | OP_ADD 
  | OP_IS_INT 
  | OP_BREDOR 
  | OP_BNOT 
  | OP_BNOR 
  | OP_PR_CNF_STAR 
  | OP_RA_JOIN 
  | OP_LE 
  | OP_SET_UNION 
  | OP_PR_UNDEF 
  | OP_BREDAND 
  | OP_LT 
  | OP_RA_UNION 
  | OP_BADD 
  | OP_BUREM0 
  | OP_OEQ 
  | OP_PR_MODUS_PONENS 
  | OP_RA_CLONE 
  | OP_REPEAT 
  | OP_RA_NEGATION_FILTER 
  | OP_BSMOD0 
  | OP_BLSHR 
  | OP_BASHR 
  | OP_PR_UNIT_RESOLUTION 
  | OP_ROTATE_RIGHT 
  | OP_ARRAY_DEFAULT 
  | OP_PR_PULL_QUANT 
  | OP_PR_APPLY_DEF 
  | OP_PR_REWRITE_STAR 
  | OP_IDIV 
  | OP_PR_GOAL 
  | OP_PR_IFF_TRUE 
  | OP_LABEL_LIT 
  | OP_BOR 
  | OP_PR_SYMMETRY 
  | OP_TRUE 
  | OP_SET_COMPLEMENT 
  | OP_CONCAT 
  | OP_PR_NOT_OR_ELIM 
  | OP_IFF 
  | OP_BSHL 
  | OP_PR_TRANSITIVITY 
  | OP_SGT 
  | OP_RA_WIDEN 
  | OP_PR_DEF_INTRO 
  | OP_NOT 
  | OP_PR_QUANT_INTRO 
  | OP_UGT 
  | OP_DT_RECOGNISER 
  | OP_SET_INTERSECT 
  | OP_BSREM 
  | OP_RA_STORE 
  | OP_SLT 
  | OP_ROTATE_LEFT 
  | OP_PR_NNF_NEG 
  | OP_PR_REFLEXIVITY 
  | OP_ULEQ 
  | OP_BIT1 
  | OP_BIT0 
  | OP_EQ 
  | OP_BMUL 
  | OP_ARRAY_MAP 
  | OP_STORE 
  | OP_PR_HYPOTHESIS 
  | OP_RA_RENAME 
  | OP_AND 
  | OP_TO_REAL 
  | OP_PR_NNF_POS 
  | OP_PR_AND_ELIM 
  | OP_MOD 
  | OP_BUDIV0 
  | OP_PR_TRUE 
  | OP_BNAND 
  | OP_PR_ELIM_UNUSED_VARS 
  | OP_RA_FILTER 
  | OP_FD_LT 
  | OP_RA_EMPTY 
  | OP_DIV 
  | OP_ANUM 
  | OP_MUL 
  | OP_UGEQ 
  | OP_BSREM0 
  | OP_PR_TH_LEMMA 
  | OP_BXOR 
  | OP_DISTINCT 
  | OP_PR_IFF_FALSE 
  | OP_BV2INT 
  | OP_EXT_ROTATE_LEFT 
  | OP_PR_PULL_QUANT_STAR 
  | OP_BSUB 
  | OP_PR_ASSERTED 
  | OP_BXNOR 
  | OP_EXTRACT 
  | OP_PR_DER 
  | OP_DT_CONSTRUCTOR 
  | OP_GT 
  | OP_BUREM 
  | OP_IMPLIES 
  | OP_SLEQ 
  | OP_GE 
  | OP_BAND 
  | OP_ITE 
  | OP_AS_ARRAY 
  | OP_RA_SELECT 
  | OP_CONST_ARRAY 
  | OP_BSDIV 
  | OP_OR 
  | OP_PR_HYPER_RESOLVE 
  | OP_AGNUM 
  | OP_PR_PUSH_QUANT 
  | OP_BSMOD 
  | OP_PR_IFF_OEQ 
  | OP_INTERP 
  | OP_PR_LEMMA 
  | OP_SET_SUBSET 
  | OP_SELECT 
  | OP_RA_PROJECT 
  | OP_BNEG 
  | OP_UMINUS 
  | OP_REM 
  | OP_TO_INT 
  | OP_PR_QUANT_INST 
  | OP_SGEQ 
  | OP_POWER 
  | OP_XOR3 
  | OP_RA_IS_EMPTY 
  | OP_CARRY 
  | OP_DT_ACCESSOR 
  | OP_PR_TRANSITIVITY_STAR 
  | OP_PR_NNF_STAR 
  | OP_PR_COMMUTATIVITY 
  | OP_ULT 
  | OP_BSDIV0 
  | OP_SET_DIFFERENCE 
  | OP_INT2BV 
  | OP_XOR 
  | OP_PR_MODUS_PONENS_OEQ 
  | OP_BNUM 
  | OP_BUDIV 
  | OP_PR_MONOTONICITY 
  | OP_PR_DEF_AXIOM 
  | OP_FALSE 
  | OP_EXT_ROTATE_RIGHT 
  | OP_PR_DISTRIBUTIVITY 
  | OP_SIGN_EXT 
  | OP_PR_SKOLEMIZE 
  | OP_BCOMP 
  | OP_RA_COMPLEMENT 

(** Convert decl_kind to int*)
val int_of_decl_kind : decl_kind -> int
(** Convert int to decl_kind*)
val decl_kind_of_int : int -> decl_kind

(** param_kind *)
type param_kind =
  | PK_BOOL 
  | PK_SYMBOL 
  | PK_OTHER 
  | PK_INVALID 
  | PK_UINT 
  | PK_STRING 
  | PK_DOUBLE 

(** Convert param_kind to int*)
val int_of_param_kind : param_kind -> int
(** Convert int to param_kind*)
val param_kind_of_int : int -> param_kind

(** ast_print_mode *)
type ast_print_mode =
  | PRINT_SMTLIB2_COMPLIANT 
  | PRINT_SMTLIB_COMPLIANT 
  | PRINT_SMTLIB_FULL 
  | PRINT_LOW_LEVEL 

(** Convert ast_print_mode to int*)
val int_of_ast_print_mode : ast_print_mode -> int
(** Convert int to ast_print_mode*)
val ast_print_mode_of_int : int -> ast_print_mode

(** error_code *)
type error_code =
  | INVALID_PATTERN 
  | MEMOUT_FAIL 
  | NO_PARSER 
  | OK 
  | INVALID_ARG 
  | EXCEPTION 
  | IOB 
  | INTERNAL_FATAL 
  | INVALID_USAGE 
  | FILE_ACCESS_ERROR 
  | SORT_ERROR 
  | PARSER_ERROR 
  | DEC_REF_ERROR 

(** Convert error_code to int*)
val int_of_error_code : error_code -> int
(** Convert int to error_code*)
val error_code_of_int : int -> error_code

(** goal_prec *)
type goal_prec =
  | GOAL_UNDER 
  | GOAL_PRECISE 
  | GOAL_UNDER_OVER 
  | GOAL_OVER 

(** Convert goal_prec to int*)
val int_of_goal_prec : goal_prec -> int
(** Convert int to goal_prec*)
val goal_prec_of_int : int -> goal_prec

