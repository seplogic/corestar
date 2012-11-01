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
type spec = Spec.ast_spec HashSet.t

type call_core =
  { call_name : string
  ; call_rets : args_out
  ; call_args : args_in }

type 'a procedure =
  { proc_name : string
  ; proc_spec : spec
  ; proc_body : 'a option }

type assignment_core =
  { asgn_rets : args_out
  ; asgn_args : args_in
  ; asgn_spec : spec }

type core_statement =
    Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of assignment_core
  | Call_core of call_core
  | Goto_stmt_core of string list
  | End
type symb_question = core_statement list procedure
type symb_test = symb_question * bool (* snd is expected answer *)
