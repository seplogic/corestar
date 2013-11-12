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
  fprintf f "@[{%a}@]@,@[(%a)@]@,@[{%a}@]"
    Expr.pp pre
    (pp_list_sep "," pp_string) modifies
    Expr.pp post

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
      fprintf f "@[goto %a;@]" (pp_list_sep "," pp_string) ls
  | End -> fprintf f "@[end;@]"

let pp_logic _ _ = failwith "TODO (a8d7bnw2w)"

let pp_ast_procedure f { proc_name; proc_spec; proc_body } =
  let pp_body f body =
    let pp_nl_core f c = fprintf f "@\n%a" pp_statement c in
    fprintf f "@\n@[<2>?%a@]" (pp_list pp_nl_core) body in
  fprintf f "@\n@[";
  fprintf f "@[<2>procedure %s :@\n%a@]" proc_name pp_spec proc_spec;
  option () (pp_body f) proc_body;
  fprintf f "@]"

let pp_rules f { calculus; abstraction } =
  fprintf f "@[%a@\n%a@]"
    (pp_list CalculusOps.pp_rule_schema) calculus
    (pp_list AbstractionOps.pp_rule_schema) abstraction

let pp_ast_question f { q_procs; q_rules; q_infer; q_name } =
  fprintf f "@[<2>question %s@\ninfer %b@\n%a@\n%a@]"
    q_name
    q_infer
    (pp_list pp_ast_procedure) q_procs
    pp_rules q_rules

(* TODO: simpler names for args/rets. *)
let return n = Printf.sprintf "$ret_v%d" n
let parameter n = Printf.sprintf "@parameter%d:" n

let global_prefix = "$g"

let is_parameter = StringH.starts_with "@parameter"
let is_return = StringH.starts_with "$ret"
let is_global = StringH.starts_with global_prefix

let empty_ast_question =
  { q_procs = []
  ; q_globals = []
  ; q_rules = { calculus = []; abstraction = [] }
  ; q_infer = false
  ; q_name = "empty_question" }

type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool

let refines_triple calculus triple1 triple2 =
  let ( => ) = Prover.is_entailment calculus in
  (triple2.pre => triple1.pre) && (triple1.post => triple2.post)

let refines_spec logic spec1 spec2 =
  TripleSet.for_all
    (fun t2 -> TripleSet.exists (fun t1 -> refines_triple logic t1 t2) spec1)
    spec2

let mk_assume f =
  TripleSet.singleton { pre = Expr.emp; post = f; modifies = [] }
let mk_assert f =
  TripleSet.singleton { pre = f; post = f; modifies = [] }
