(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/core.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

type args_out = Vars.var list
type args_in = Psyntax.args list

type 'a triple = { pre : 'a; post : 'a }
type ast_triple = Psyntax.form triple
type inner_triple = Sepprover.inner_form triple
type 'a spec = 'a HashSet.t
type ast_spec = ast_triple spec
type inner_spec = inner_triple spec

type call_core =
  { call_name : string
  ; call_rets : args_out
  ; call_args : args_in }

type ('body, 'spec) procedure =
  { proc_name : string
  ; mutable proc_spec : 'spec
  ; proc_body : 'body option
  ; proc_rules : Psyntax.logic }

type 'spec assignment_core =
  { asgn_rets : args_out
  ; asgn_args : args_in
  ; asgn_spec : 'spec }

type 'spec core_statement =
  | Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of 'spec assignment_core
  | Call_core of call_core
  | Goto_stmt_core of string list
  | End

type ast_core = ast_spec core_statement
type inner_core = inner_spec core_statement

type ast_procedure = (ast_core list, ast_spec) procedure

type question =
  { q_procs : ast_procedure list
  ; q_rules : Psyntax.logic
  ; q_infer : bool  (* [true] means do bi-abduction *)
  ; q_name : string }

