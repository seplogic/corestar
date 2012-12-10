(********************************************************
   This file is part of coreStar
        src/symexec_ast/pp_core.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Format

module C = Core
module P = Sepprover
module PS = Psyntax
module S = Spec


(** Pretty printer for core programs. *)

let pp_args_out = pp_list_sep "," Vars.pp_var
let pp_args_in = pp_list_sep "," PS.string_args

let pp_spec pf f { S.pre; post } =
  fprintf f "@[@[{%a}@]@[{%a}@]@]" pf pre pf post

let pp_ast_spec = pp_spec PS.string_form
let pp_inner_spec = pp_spec P.string_inner_form

let pp_core pp_spec f = function
  | C.Nop_stmt_core -> fprintf f "nop;"
  | C.Label_stmt_core l -> fprintf f "label %s;" l
  | C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec } ->
      fprintf f "@[<2>assign@ @[%a@]@,:=@[@[%a@]@[(%a)@]@];@]"
        pp_args_out asgn_rets pp_spec asgn_spec pp_args_in asgn_args
  | C.Call_core { C.call_name; call_rets; call_args } ->
      fprintf f "@[<2>call @[%a@]@,:=@[%s@[(%a)@]@];@]"
        pp_args_out call_rets call_name pp_args_in call_args
  | C.Goto_stmt_core ls ->
      fprintf f "goto %a;" (pp_list_sep "," pp_string) ls
  | C.End -> fprintf f "end;"

let pp_ast_core = pp_core pp_ast_spec
let pp_inner_core = pp_core pp_inner_spec
