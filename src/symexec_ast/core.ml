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
type 'a spec = 'a HashSet.t
type ast_spec = Spec.ast_spec spec
type inner_spec = Spec.inner_spec spec

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

type question =
  { q_procs : (ast_core list, ast_spec) procedure list
  ; q_rules : Psyntax.logic
  ; q_infer : bool  (* [true] means do bi-abduction *)
  ; q_name : string }

(* Deprecated. Do NOT use. *)
type 'spec symb_question = ('spec core_statement list, 'spec) procedure
type 'spec symb_test = 'spec symb_question * bool (* snd is expected answer *)

