(* Automatically generated file *)

(** The enumeration types of Z3. *)

(** lbool *)
type lbool =
  | L_TRUE 
  | L_UNDEF 
  | L_FALSE 

(** Convert lbool to int*)
let int_of_lbool x : int =
  match x with
  | L_TRUE -> 1
  | L_UNDEF -> 0
  | L_FALSE -> -1

(** Convert int to lbool*)
let lbool_of_int x : lbool =
  match x with
  | 1 -> L_TRUE
  | 0 -> L_UNDEF
  | -1 -> L_FALSE
  | _ -> raise (Failure "undefined enum value")

(** symbol_kind *)
type symbol_kind =
  | INT_SYMBOL 
  | STRING_SYMBOL 

(** Convert symbol_kind to int*)
let int_of_symbol_kind x : int =
  match x with
  | INT_SYMBOL -> 0
  | STRING_SYMBOL -> 1

(** Convert int to symbol_kind*)
let symbol_kind_of_int x : symbol_kind =
  match x with
  | 0 -> INT_SYMBOL
  | 1 -> STRING_SYMBOL
  | _ -> raise (Failure "undefined enum value")

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
let int_of_parameter_kind x : int =
  match x with
  | PARAMETER_FUNC_DECL -> 6
  | PARAMETER_DOUBLE -> 1
  | PARAMETER_SYMBOL -> 3
  | PARAMETER_INT -> 0
  | PARAMETER_AST -> 5
  | PARAMETER_SORT -> 4
  | PARAMETER_RATIONAL -> 2

(** Convert int to parameter_kind*)
let parameter_kind_of_int x : parameter_kind =
  match x with
  | 6 -> PARAMETER_FUNC_DECL
  | 1 -> PARAMETER_DOUBLE
  | 3 -> PARAMETER_SYMBOL
  | 0 -> PARAMETER_INT
  | 5 -> PARAMETER_AST
  | 4 -> PARAMETER_SORT
  | 2 -> PARAMETER_RATIONAL
  | _ -> raise (Failure "undefined enum value")

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
let int_of_sort_kind x : int =
  match x with
  | BV_SORT -> 4
  | FINITE_DOMAIN_SORT -> 8
  | ARRAY_SORT -> 5
  | UNKNOWN_SORT -> 1000
  | RELATION_SORT -> 7
  | REAL_SORT -> 3
  | INT_SORT -> 2
  | UNINTERPRETED_SORT -> 0
  | BOOL_SORT -> 1
  | DATATYPE_SORT -> 6

(** Convert int to sort_kind*)
let sort_kind_of_int x : sort_kind =
  match x with
  | 4 -> BV_SORT
  | 8 -> FINITE_DOMAIN_SORT
  | 5 -> ARRAY_SORT
  | 1000 -> UNKNOWN_SORT
  | 7 -> RELATION_SORT
  | 3 -> REAL_SORT
  | 2 -> INT_SORT
  | 0 -> UNINTERPRETED_SORT
  | 1 -> BOOL_SORT
  | 6 -> DATATYPE_SORT
  | _ -> raise (Failure "undefined enum value")

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
let int_of_ast_kind x : int =
  match x with
  | VAR_AST -> 2
  | SORT_AST -> 4
  | QUANTIFIER_AST -> 3
  | UNKNOWN_AST -> 1000
  | FUNC_DECL_AST -> 5
  | NUMERAL_AST -> 0
  | APP_AST -> 1

(** Convert int to ast_kind*)
let ast_kind_of_int x : ast_kind =
  match x with
  | 2 -> VAR_AST
  | 4 -> SORT_AST
  | 3 -> QUANTIFIER_AST
  | 1000 -> UNKNOWN_AST
  | 5 -> FUNC_DECL_AST
  | 0 -> NUMERAL_AST
  | 1 -> APP_AST
  | _ -> raise (Failure "undefined enum value")

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
let int_of_decl_kind x : int =
  match x with
  | OP_LABEL -> 1792
  | OP_PR_REWRITE -> 1294
  | OP_UNINTERPRETED -> 2051
  | OP_SUB -> 519
  | OP_ZERO_EXT -> 1058
  | OP_ADD -> 518
  | OP_IS_INT -> 528
  | OP_BREDOR -> 1061
  | OP_BNOT -> 1051
  | OP_BNOR -> 1054
  | OP_PR_CNF_STAR -> 1315
  | OP_RA_JOIN -> 1539
  | OP_LE -> 514
  | OP_SET_UNION -> 773
  | OP_PR_UNDEF -> 1280
  | OP_BREDAND -> 1062
  | OP_LT -> 516
  | OP_RA_UNION -> 1540
  | OP_BADD -> 1028
  | OP_BUREM0 -> 1039
  | OP_OEQ -> 267
  | OP_PR_MODUS_PONENS -> 1284
  | OP_RA_CLONE -> 1548
  | OP_REPEAT -> 1060
  | OP_RA_NEGATION_FILTER -> 1544
  | OP_BSMOD0 -> 1040
  | OP_BLSHR -> 1065
  | OP_BASHR -> 1066
  | OP_PR_UNIT_RESOLUTION -> 1304
  | OP_ROTATE_RIGHT -> 1068
  | OP_ARRAY_DEFAULT -> 772
  | OP_PR_PULL_QUANT -> 1296
  | OP_PR_APPLY_DEF -> 1310
  | OP_PR_REWRITE_STAR -> 1295
  | OP_IDIV -> 523
  | OP_PR_GOAL -> 1283
  | OP_PR_IFF_TRUE -> 1305
  | OP_LABEL_LIT -> 1793
  | OP_BOR -> 1050
  | OP_PR_SYMMETRY -> 1286
  | OP_TRUE -> 256
  | OP_SET_COMPLEMENT -> 776
  | OP_CONCAT -> 1056
  | OP_PR_NOT_OR_ELIM -> 1293
  | OP_IFF -> 263
  | OP_BSHL -> 1064
  | OP_PR_TRANSITIVITY -> 1287
  | OP_SGT -> 1048
  | OP_RA_WIDEN -> 1541
  | OP_PR_DEF_INTRO -> 1309
  | OP_NOT -> 265
  | OP_PR_QUANT_INTRO -> 1290
  | OP_UGT -> 1047
  | OP_DT_RECOGNISER -> 2049
  | OP_SET_INTERSECT -> 774
  | OP_BSREM -> 1033
  | OP_RA_STORE -> 1536
  | OP_SLT -> 1046
  | OP_ROTATE_LEFT -> 1067
  | OP_PR_NNF_NEG -> 1313
  | OP_PR_REFLEXIVITY -> 1285
  | OP_ULEQ -> 1041
  | OP_BIT1 -> 1025
  | OP_BIT0 -> 1026
  | OP_EQ -> 258
  | OP_BMUL -> 1030
  | OP_ARRAY_MAP -> 771
  | OP_STORE -> 768
  | OP_PR_HYPOTHESIS -> 1302
  | OP_RA_RENAME -> 1545
  | OP_AND -> 261
  | OP_TO_REAL -> 526
  | OP_PR_NNF_POS -> 1312
  | OP_PR_AND_ELIM -> 1292
  | OP_MOD -> 525
  | OP_BUDIV0 -> 1037
  | OP_PR_TRUE -> 1281
  | OP_BNAND -> 1053
  | OP_PR_ELIM_UNUSED_VARS -> 1299
  | OP_RA_FILTER -> 1543
  | OP_FD_LT -> 1549
  | OP_RA_EMPTY -> 1537
  | OP_DIV -> 522
  | OP_ANUM -> 512
  | OP_MUL -> 521
  | OP_UGEQ -> 1043
  | OP_BSREM0 -> 1038
  | OP_PR_TH_LEMMA -> 1318
  | OP_BXOR -> 1052
  | OP_DISTINCT -> 259
  | OP_PR_IFF_FALSE -> 1306
  | OP_BV2INT -> 1072
  | OP_EXT_ROTATE_LEFT -> 1069
  | OP_PR_PULL_QUANT_STAR -> 1297
  | OP_BSUB -> 1029
  | OP_PR_ASSERTED -> 1282
  | OP_BXNOR -> 1055
  | OP_EXTRACT -> 1059
  | OP_PR_DER -> 1300
  | OP_DT_CONSTRUCTOR -> 2048
  | OP_GT -> 517
  | OP_BUREM -> 1034
  | OP_IMPLIES -> 266
  | OP_SLEQ -> 1042
  | OP_GE -> 515
  | OP_BAND -> 1049
  | OP_ITE -> 260
  | OP_AS_ARRAY -> 778
  | OP_RA_SELECT -> 1547
  | OP_CONST_ARRAY -> 770
  | OP_BSDIV -> 1031
  | OP_OR -> 262
  | OP_PR_HYPER_RESOLVE -> 1319
  | OP_AGNUM -> 513
  | OP_PR_PUSH_QUANT -> 1298
  | OP_BSMOD -> 1035
  | OP_PR_IFF_OEQ -> 1311
  | OP_INTERP -> 268
  | OP_PR_LEMMA -> 1303
  | OP_SET_SUBSET -> 777
  | OP_SELECT -> 769
  | OP_RA_PROJECT -> 1542
  | OP_BNEG -> 1027
  | OP_UMINUS -> 520
  | OP_REM -> 524
  | OP_TO_INT -> 527
  | OP_PR_QUANT_INST -> 1301
  | OP_SGEQ -> 1044
  | OP_POWER -> 529
  | OP_XOR3 -> 1074
  | OP_RA_IS_EMPTY -> 1538
  | OP_CARRY -> 1073
  | OP_DT_ACCESSOR -> 2050
  | OP_PR_TRANSITIVITY_STAR -> 1288
  | OP_PR_NNF_STAR -> 1314
  | OP_PR_COMMUTATIVITY -> 1307
  | OP_ULT -> 1045
  | OP_BSDIV0 -> 1036
  | OP_SET_DIFFERENCE -> 775
  | OP_INT2BV -> 1071
  | OP_XOR -> 264
  | OP_PR_MODUS_PONENS_OEQ -> 1317
  | OP_BNUM -> 1024
  | OP_BUDIV -> 1032
  | OP_PR_MONOTONICITY -> 1289
  | OP_PR_DEF_AXIOM -> 1308
  | OP_FALSE -> 257
  | OP_EXT_ROTATE_RIGHT -> 1070
  | OP_PR_DISTRIBUTIVITY -> 1291
  | OP_SIGN_EXT -> 1057
  | OP_PR_SKOLEMIZE -> 1316
  | OP_BCOMP -> 1063
  | OP_RA_COMPLEMENT -> 1546

(** Convert int to decl_kind*)
let decl_kind_of_int x : decl_kind =
  match x with
  | 1792 -> OP_LABEL
  | 1294 -> OP_PR_REWRITE
  | 2051 -> OP_UNINTERPRETED
  | 519 -> OP_SUB
  | 1058 -> OP_ZERO_EXT
  | 518 -> OP_ADD
  | 528 -> OP_IS_INT
  | 1061 -> OP_BREDOR
  | 1051 -> OP_BNOT
  | 1054 -> OP_BNOR
  | 1315 -> OP_PR_CNF_STAR
  | 1539 -> OP_RA_JOIN
  | 514 -> OP_LE
  | 773 -> OP_SET_UNION
  | 1280 -> OP_PR_UNDEF
  | 1062 -> OP_BREDAND
  | 516 -> OP_LT
  | 1540 -> OP_RA_UNION
  | 1028 -> OP_BADD
  | 1039 -> OP_BUREM0
  | 267 -> OP_OEQ
  | 1284 -> OP_PR_MODUS_PONENS
  | 1548 -> OP_RA_CLONE
  | 1060 -> OP_REPEAT
  | 1544 -> OP_RA_NEGATION_FILTER
  | 1040 -> OP_BSMOD0
  | 1065 -> OP_BLSHR
  | 1066 -> OP_BASHR
  | 1304 -> OP_PR_UNIT_RESOLUTION
  | 1068 -> OP_ROTATE_RIGHT
  | 772 -> OP_ARRAY_DEFAULT
  | 1296 -> OP_PR_PULL_QUANT
  | 1310 -> OP_PR_APPLY_DEF
  | 1295 -> OP_PR_REWRITE_STAR
  | 523 -> OP_IDIV
  | 1283 -> OP_PR_GOAL
  | 1305 -> OP_PR_IFF_TRUE
  | 1793 -> OP_LABEL_LIT
  | 1050 -> OP_BOR
  | 1286 -> OP_PR_SYMMETRY
  | 256 -> OP_TRUE
  | 776 -> OP_SET_COMPLEMENT
  | 1056 -> OP_CONCAT
  | 1293 -> OP_PR_NOT_OR_ELIM
  | 263 -> OP_IFF
  | 1064 -> OP_BSHL
  | 1287 -> OP_PR_TRANSITIVITY
  | 1048 -> OP_SGT
  | 1541 -> OP_RA_WIDEN
  | 1309 -> OP_PR_DEF_INTRO
  | 265 -> OP_NOT
  | 1290 -> OP_PR_QUANT_INTRO
  | 1047 -> OP_UGT
  | 2049 -> OP_DT_RECOGNISER
  | 774 -> OP_SET_INTERSECT
  | 1033 -> OP_BSREM
  | 1536 -> OP_RA_STORE
  | 1046 -> OP_SLT
  | 1067 -> OP_ROTATE_LEFT
  | 1313 -> OP_PR_NNF_NEG
  | 1285 -> OP_PR_REFLEXIVITY
  | 1041 -> OP_ULEQ
  | 1025 -> OP_BIT1
  | 1026 -> OP_BIT0
  | 258 -> OP_EQ
  | 1030 -> OP_BMUL
  | 771 -> OP_ARRAY_MAP
  | 768 -> OP_STORE
  | 1302 -> OP_PR_HYPOTHESIS
  | 1545 -> OP_RA_RENAME
  | 261 -> OP_AND
  | 526 -> OP_TO_REAL
  | 1312 -> OP_PR_NNF_POS
  | 1292 -> OP_PR_AND_ELIM
  | 525 -> OP_MOD
  | 1037 -> OP_BUDIV0
  | 1281 -> OP_PR_TRUE
  | 1053 -> OP_BNAND
  | 1299 -> OP_PR_ELIM_UNUSED_VARS
  | 1543 -> OP_RA_FILTER
  | 1549 -> OP_FD_LT
  | 1537 -> OP_RA_EMPTY
  | 522 -> OP_DIV
  | 512 -> OP_ANUM
  | 521 -> OP_MUL
  | 1043 -> OP_UGEQ
  | 1038 -> OP_BSREM0
  | 1318 -> OP_PR_TH_LEMMA
  | 1052 -> OP_BXOR
  | 259 -> OP_DISTINCT
  | 1306 -> OP_PR_IFF_FALSE
  | 1072 -> OP_BV2INT
  | 1069 -> OP_EXT_ROTATE_LEFT
  | 1297 -> OP_PR_PULL_QUANT_STAR
  | 1029 -> OP_BSUB
  | 1282 -> OP_PR_ASSERTED
  | 1055 -> OP_BXNOR
  | 1059 -> OP_EXTRACT
  | 1300 -> OP_PR_DER
  | 2048 -> OP_DT_CONSTRUCTOR
  | 517 -> OP_GT
  | 1034 -> OP_BUREM
  | 266 -> OP_IMPLIES
  | 1042 -> OP_SLEQ
  | 515 -> OP_GE
  | 1049 -> OP_BAND
  | 260 -> OP_ITE
  | 778 -> OP_AS_ARRAY
  | 1547 -> OP_RA_SELECT
  | 770 -> OP_CONST_ARRAY
  | 1031 -> OP_BSDIV
  | 262 -> OP_OR
  | 1319 -> OP_PR_HYPER_RESOLVE
  | 513 -> OP_AGNUM
  | 1298 -> OP_PR_PUSH_QUANT
  | 1035 -> OP_BSMOD
  | 1311 -> OP_PR_IFF_OEQ
  | 268 -> OP_INTERP
  | 1303 -> OP_PR_LEMMA
  | 777 -> OP_SET_SUBSET
  | 769 -> OP_SELECT
  | 1542 -> OP_RA_PROJECT
  | 1027 -> OP_BNEG
  | 520 -> OP_UMINUS
  | 524 -> OP_REM
  | 527 -> OP_TO_INT
  | 1301 -> OP_PR_QUANT_INST
  | 1044 -> OP_SGEQ
  | 529 -> OP_POWER
  | 1074 -> OP_XOR3
  | 1538 -> OP_RA_IS_EMPTY
  | 1073 -> OP_CARRY
  | 2050 -> OP_DT_ACCESSOR
  | 1288 -> OP_PR_TRANSITIVITY_STAR
  | 1314 -> OP_PR_NNF_STAR
  | 1307 -> OP_PR_COMMUTATIVITY
  | 1045 -> OP_ULT
  | 1036 -> OP_BSDIV0
  | 775 -> OP_SET_DIFFERENCE
  | 1071 -> OP_INT2BV
  | 264 -> OP_XOR
  | 1317 -> OP_PR_MODUS_PONENS_OEQ
  | 1024 -> OP_BNUM
  | 1032 -> OP_BUDIV
  | 1289 -> OP_PR_MONOTONICITY
  | 1308 -> OP_PR_DEF_AXIOM
  | 257 -> OP_FALSE
  | 1070 -> OP_EXT_ROTATE_RIGHT
  | 1291 -> OP_PR_DISTRIBUTIVITY
  | 1057 -> OP_SIGN_EXT
  | 1316 -> OP_PR_SKOLEMIZE
  | 1063 -> OP_BCOMP
  | 1546 -> OP_RA_COMPLEMENT
  | _ -> raise (Failure "undefined enum value")

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
let int_of_param_kind x : int =
  match x with
  | PK_BOOL -> 1
  | PK_SYMBOL -> 3
  | PK_OTHER -> 5
  | PK_INVALID -> 6
  | PK_UINT -> 0
  | PK_STRING -> 4
  | PK_DOUBLE -> 2

(** Convert int to param_kind*)
let param_kind_of_int x : param_kind =
  match x with
  | 1 -> PK_BOOL
  | 3 -> PK_SYMBOL
  | 5 -> PK_OTHER
  | 6 -> PK_INVALID
  | 0 -> PK_UINT
  | 4 -> PK_STRING
  | 2 -> PK_DOUBLE
  | _ -> raise (Failure "undefined enum value")

(** ast_print_mode *)
type ast_print_mode =
  | PRINT_SMTLIB2_COMPLIANT 
  | PRINT_SMTLIB_COMPLIANT 
  | PRINT_SMTLIB_FULL 
  | PRINT_LOW_LEVEL 

(** Convert ast_print_mode to int*)
let int_of_ast_print_mode x : int =
  match x with
  | PRINT_SMTLIB2_COMPLIANT -> 3
  | PRINT_SMTLIB_COMPLIANT -> 2
  | PRINT_SMTLIB_FULL -> 0
  | PRINT_LOW_LEVEL -> 1

(** Convert int to ast_print_mode*)
let ast_print_mode_of_int x : ast_print_mode =
  match x with
  | 3 -> PRINT_SMTLIB2_COMPLIANT
  | 2 -> PRINT_SMTLIB_COMPLIANT
  | 0 -> PRINT_SMTLIB_FULL
  | 1 -> PRINT_LOW_LEVEL
  | _ -> raise (Failure "undefined enum value")

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
let int_of_error_code x : int =
  match x with
  | INVALID_PATTERN -> 6
  | MEMOUT_FAIL -> 7
  | NO_PARSER -> 5
  | OK -> 0
  | INVALID_ARG -> 3
  | EXCEPTION -> 12
  | IOB -> 2
  | INTERNAL_FATAL -> 9
  | INVALID_USAGE -> 10
  | FILE_ACCESS_ERROR -> 8
  | SORT_ERROR -> 1
  | PARSER_ERROR -> 4
  | DEC_REF_ERROR -> 11

(** Convert int to error_code*)
let error_code_of_int x : error_code =
  match x with
  | 6 -> INVALID_PATTERN
  | 7 -> MEMOUT_FAIL
  | 5 -> NO_PARSER
  | 0 -> OK
  | 3 -> INVALID_ARG
  | 12 -> EXCEPTION
  | 2 -> IOB
  | 9 -> INTERNAL_FATAL
  | 10 -> INVALID_USAGE
  | 8 -> FILE_ACCESS_ERROR
  | 1 -> SORT_ERROR
  | 4 -> PARSER_ERROR
  | 11 -> DEC_REF_ERROR
  | _ -> raise (Failure "undefined enum value")

(** goal_prec *)
type goal_prec =
  | GOAL_UNDER 
  | GOAL_PRECISE 
  | GOAL_UNDER_OVER 
  | GOAL_OVER 

(** Convert goal_prec to int*)
let int_of_goal_prec x : int =
  match x with
  | GOAL_UNDER -> 1
  | GOAL_PRECISE -> 0
  | GOAL_UNDER_OVER -> 3
  | GOAL_OVER -> 2

(** Convert int to goal_prec*)
let goal_prec_of_int x : goal_prec =
  match x with
  | 1 -> GOAL_UNDER
  | 0 -> GOAL_PRECISE
  | 3 -> GOAL_UNDER_OVER
  | 2 -> GOAL_OVER
  | _ -> raise (Failure "undefined enum value")

