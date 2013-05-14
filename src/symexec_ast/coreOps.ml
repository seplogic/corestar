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

let ast_to_inner_triple { pre; post } =
  let f = Sepprover.convert in { pre = f pre; post = f post }

let ast_to_inner_spec = HashSet.map ast_to_inner_triple

let ast_to_inner_core = function
  | Nop_stmt_core -> Nop_stmt_core
  | Label_stmt_core l -> Label_stmt_core l
  | Assignment_core c ->
      Assignment_core { c with asgn_spec = ast_to_inner_spec c.asgn_spec }
  | Call_core c -> Call_core c
  | Goto_stmt_core ls -> Goto_stmt_core ls
  | End -> End

let pp_args_out = pp_list_sep "," Vars.pp_var
let pp_args_in = pp_list_sep "," Psyntax.string_args

let pp_triple pf f { pre; post } =
  fprintf f "{%a}@,{%a}" pf pre pf post
let pp_ast_triple = pp_triple Psyntax.string_form
let pp_inner_triple = pp_triple Sepprover.string_inner_form

let pp_spec pf f ts = pp_list_sep " " (pp_triple pf) f (HashSet.elements ts)
let pp_ast_spec = pp_spec Psyntax.string_form
let pp_inner_spec = pp_spec Sepprover.string_inner_form

let pp_core pp_spec f = function
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

let pp_ast_core = pp_core pp_ast_spec
let pp_inner_core = pp_core pp_inner_spec

let pp_logic _ _ = failwith "XXX"

let pp_proc pp_spec f { proc_name; proc_spec; proc_body } =
  let pp_body f body =
    let pp_nl_core f c = fprintf f "@\n%a" (pp_core pp_spec) c in
    fprintf f "@\n@[<2>?%a@]" (pp_list pp_nl_core) body in
  fprintf f "@\n@[";
  fprintf f "@[<2>procedure %s :@\n%a@]" proc_name pp_spec proc_spec;
  option () (pp_body f) proc_body;
  fprintf f "@]"

let pp_ast_proc = pp_proc pp_ast_spec

let pp_ast_question f { q_procs; q_rules; q_infer; q_name } =
  fprintf f "@[infer %b@@\n%a@\n%a@]"
    q_infer
    (pp_list pp_ast_proc) q_procs
    pp_logic q_rules

let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1
let return_var n = Vars.concretep_str (Printf.sprintf "$ret_v%d" n)
let parameter n = Printf.sprintf "@parameter%d:" n
let parameter_var n = (Vars.concretep_str (parameter n))

let empty_question empty_logic =
  { q_procs = []
  ; q_rules = empty_logic
  ; q_infer = false
  ; q_name = "empty_question" }
