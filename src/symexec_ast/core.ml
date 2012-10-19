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



type call_core = {
  call_rets : Vars.var list;
  call_args : Psyntax.args list;
  call_spec : Spec.spec HashSet.t
}

type 'a procedure = {
  proc_name : string;
  proc_spec : Spec.spec;
  proc_body : 'a
}

type core_statement =
    Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of call_core
  | Call_core of string * call_core (* TODO: move specs centrally *)
  | Goto_stmt_core of string list
  | End
type symb_question = core_statement list procedure
type symb_test = symb_question * bool (* snd is expected answer *)
