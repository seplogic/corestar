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
module PS = Psyntax
module S = Spec


(** Pretty printer for core programs. *)

let pp_args_out = pp_list_sep "," Vars.pp_var
let pp_args_in = pp_list_sep "," PS.string_args

let pp_triple f { S.pre; post } =
  fprintf f "@[@[{%a}@]@[{%a}@]@]" PS.string_form pre PS.string_form post

let pp_spec f ts = pp_list_sep " " pp_triple f (HashSet.elements ts)

let pp_stmt_core ppf = function
  | C.Nop_stmt_core -> fprintf ppf "nop;"
  | C.Label_stmt_core l -> fprintf ppf "label %s;" l
  | C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec } ->
      fprintf ppf "@[<2>assign@ @[%a@]@,:=@[@[%a@]@[(%a)@]@];@]"
        pp_args_out asgn_rets pp_spec asgn_spec pp_args_in asgn_args
  | C.Call_core { C.call_name; call_rets; call_args } ->
      fprintf ppf "@[<2>call @[%a@]@,:=@[%s@[(%a)@]@];@]"
        pp_args_out call_rets call_name pp_args_in call_args
  | C.Goto_stmt_core ls ->
      fprintf ppf "goto %a;" (pp_list_sep "," pp_string) ls
  | C.End -> fprintf ppf "end;"
