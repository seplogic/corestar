(********************************************************
   This file is part of coreStar
        src/utils/coreOps.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Core
open Corestar_std
open Format

module Expr = Expression

let pp_args_out = pp_list_sep "," pp_string
let pp_args_in = pp_list_sep "," Expr.pp

let pp_triple f { pre; post; modifies } =
  let pm f = function
    | None -> fprintf f "*"
    | Some vs -> fprintf f "%a:=*" (pp_list_sep "," pp_string) vs in
  fprintf f "{%a}@,[%a]@,{%a}" Expr.pp pre pm modifies Expr.pp post

let pp_spec f ts = pp_list_sep "+" pp_triple f (TripleSet.elements ts)

let pp_statement f = function
  | Nop_stmt_core -> fprintf f "nop;"
  | Label_stmt_core l -> fprintf f "label %s;" l
  | Assignment_core { asgn_rets; asgn_args; asgn_spec } ->
      fprintf f "@[<2>assign@ @[%a@]@,:=%a@,(%a);@]"
        pp_args_out asgn_rets pp_spec asgn_spec pp_args_in asgn_args
  | Call_core { call_name; call_rets; call_args } ->
      fprintf f "@[<2>call @[%a@]@,:=@[%s@[(%a)@]@];@]"
        pp_args_out call_rets call_name pp_args_in call_args
  | Goto_stmt_core ls ->
      fprintf f "goto %a;" (pp_list_sep "," pp_string) ls
  | End -> fprintf f "end;"

let pp_logic _ _ = failwith "TODO"

let pp_ast_procedure f { proc_name; proc_spec; proc_body } =
  let pp_body f body =
    let pp_nl_core f c = fprintf f "@\n%a" pp_statement c in
    fprintf f "@\n@[<2>?%a@]" (pp_list pp_nl_core) body in
  fprintf f "@\n@[";
  fprintf f "@[<2>procedure %s :@\n%a@]" proc_name pp_spec proc_spec;
  option () (pp_body f) proc_body;
  fprintf f "@]"

let pp_ast_question f { q_procs; q_rules; q_infer; q_name } =
  fprintf f "@[infer %b@@\n%a@\n%a@]"
    q_infer
    (pp_list pp_ast_procedure) q_procs
    pp_logic q_rules

let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1
let return_var n = Vars.concretep_str (Printf.sprintf "$ret_v%d" n)
let parameter n = Printf.sprintf "@parameter%d:" n
let parameter_var n = (Vars.concretep_str (parameter n))

let has_prefix p v = StringH.starts_with p (Vars.string_var v)

let global_prefix = "$g"

let is_parameter = has_prefix "@parameter"
let is_return = has_prefix "$ret"
let is_global = has_prefix global_prefix

let empty_ast_question =
  { q_procs = []
  ; q_rules = failwith "TODO: empty logic"
  ; q_infer = false
  ; q_name = "empty_question" }

type 'a refinement_check = Type.todo -> 'a -> 'a -> bool

let refines_triple logic triple1 triple2 =
  failwith "TODO"
  (*
  Sepprover.implies logic triple2.pre triple1.pre &&
  Sepprover.implies logic triple1.post triple2.post
  *)

let refines_spec logic spec1 spec2 =
  TripleSet.for_all
    (fun t2 -> TripleSet.exists (fun t1 -> refines_triple logic t1 t2) spec1)
    spec2

let mk_assume f =
  TripleSet.singleton { pre = Expr.emp; post = f; modifies = Some [] }
let mk_assert f = TripleSet.singleton { pre = f; post = f; modifies = Some [] }
