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

let pp_args_out = pp_list_sep "," Syntax.pp_expr
let pp_args_in = pp_list_sep "," Syntax.pp_expr

let pp_triple f { pre; post; modifies } =
  fprintf f "@[{%a}@]@,@[(%a)@]@,@[{%a}@]"
    Syntax.pp_expr pre
    (pp_list_sep "," Syntax.pp_expr) modifies
    Syntax.pp_expr post

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
    let pp_nl_core f c = fprintf f "@\n@{<p>%a@}" pp_statement c in
    fprintf f "@\n@[<2>?%a@]" (pp_list pp_nl_core) body in
  fprintf f "@\n@[@{<details>";
  fprintf f "@[<2>@{<summary>procedure %s :@}@\n%a@]" proc_name pp_spec proc_spec;
  option () (pp_body f) proc_body;
  fprintf f "@}@]"

let pp_rules f { calculus; abstraction } =
  fprintf f "@[%a@\n%a@]"
    (pp_list CalculusOps.pp_rule_schema) calculus
    (pp_list AbstractionOps.pp_rule_schema) abstraction

let pp_ast_question f { q_procs; q_rules; q_infer; q_name } =
  fprintf f "@[<2>@{<p>question %s@}@\n@{<p>infer %b@}@\n%a@\n%a@]"
    q_name
    q_infer
    (pp_list pp_ast_procedure) q_procs
    pp_rules q_rules

let empty_ast_question ctx =
  { q_syntax_context = ctx
  ; q_procs = []
  ; q_globals = []
  ; q_rules = { calculus = []; abstraction = [] }
  ; q_infer = false
  ; q_name = "empty_question" }

type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool

let refines_triple ctx calculus triple1 triple2 =
  (* NOTE: [infer_frame], unlike [is_entailment], instantiates lvars. *)
  let ( => ) a b = Prover.infer_frame ctx calculus a b <> [] in
  (triple2.pre => triple1.pre) && (triple1.post => triple2.post)

let refines_spec ctx logic spec1 spec2 =
  TripleSet.for_all
    (fun t2 -> TripleSet.exists (fun t1 -> refines_triple ctx logic t1 t2) spec1)
    spec2

let mk_assume ctx f =
  TripleSet.singleton { pre = Syntax.mk_emp ctx; post = f; modifies = []; in_vars = []; out_vars = [] }
let mk_assert f =
  TripleSet.singleton { pre = f; post = f; modifies = []; in_vars = []; out_vars = [] }
