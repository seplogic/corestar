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

(* XXX: This must have [proc_args] and [proc_rets]. What types, thou? *)
type ('body, 'spec) procedure =
  { proc_name : string
  ; mutable proc_spec : 'spec
  ; proc_body : 'body option }

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
type 'spec symb_question = ('spec core_statement list, 'spec) procedure
type 'spec symb_test = 'spec symb_question * bool (* snd is expected answer *)

let ast_to_inner_spec : ast_spec -> inner_spec =
  let mh f h =
    let xs = HashSet.elements h in
    let xs = List.map f xs in
    let h = HashSet.create 1 in
    List.iter (HashSet.add h) xs; h in
  mh Spec.ast_to_inner_spec

let ast_to_inner_core : ast_core -> inner_core = function
  | Nop_stmt_core -> Nop_stmt_core
  | Label_stmt_core l -> Label_stmt_core l
  | Assignment_core c ->
      Assignment_core { c with asgn_spec = ast_to_inner_spec c.asgn_spec }
  | Call_core c -> Call_core c
  | Goto_stmt_core ls -> Goto_stmt_core ls
  | End -> End
