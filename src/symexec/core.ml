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

module F = Formula

type args_out = string list
type args_in = F.t list

type triple = { pre : F.t; post : F.t; modifies : args_out option }

module TripleSet = HashSet.Make (struct
  type t = triple

  let equal a b =
    F.eq a.pre b.pre && F.eq a.post b.post && a.modifies = b.modifies

  let hash { pre; post; modifies } =
    ((F.hash pre * 31) + F.hash post) * 31 + Hashtbl.hash modifies
end)

type spec = TripleSet.t

type call =
  { call_name : string
  ; call_rets : args_out
  ; call_args : args_in }

type 'body procedure =
  { proc_name : string
  ; mutable proc_spec : spec
  ; proc_body : 'body option
  ; proc_rules : Type.todo }

type assignment =
  { asgn_rets : args_out
  ; asgn_args : args_in
  ; asgn_spec : spec }

type statement =
  | Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of assignment
  | Call_core of call
  | Goto_stmt_core of string list
  | End

type ast_procedure = statement list procedure

type 'proc question =
  { q_procs : 'proc list
  ; q_rules : Type.todo
  ; q_infer : bool  (* [true] means do bi-abduction *)
  ; q_name : string }
type ast_question = ast_procedure question
