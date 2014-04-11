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

let empty_ast_question =
  { q_procs = []
  ; q_globals = []
  ; q_rules = { calculus = []; abstraction = [] }
  ; q_infer = false
  ; q_name = "empty_question" }

type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool

let refines_triple calculus triple1 triple2 =
  (* NOTE: [infer_frame], unlike [is_entailment], instantiates lvars. *)
  let ( => ) a b = Prover.infer_frame calculus a b <> [] in
  (triple2.pre => triple1.pre) && (triple1.post => triple2.post)

let refines_spec logic spec1 spec2 =
  TripleSet.for_all
    (fun t2 -> TripleSet.exists (fun t1 -> refines_triple logic t1 t2) spec1)
    spec2

let mk_assume f =
  TripleSet.singleton { pre = Syntax.mk_emp; post = f; modifies = []; in_vars = []; out_vars = [] }
let mk_assert f =
  TripleSet.singleton { pre = f; post = f; modifies = []; in_vars = []; out_vars = [] }

(* Helpers for [check_well_formed]. *) (* {{{ *)

exception Not_well_formed

let compute_sigs ok ps =
  let h = StringHash.create 0 in
  let one_sig p =
    if StringHash.mem h p.proc_name then begin
      eprintf "procedure %s already declared@\n" p.proc_name;
      ok := false
    end;
    StringHash.replace h p.proc_name (p.proc_params, p.proc_rets) in
  List.iter one_sig ps;
  StringHash.find h

let check_sorts_match ok loc inout m xs ys =
  let rec f n = function
    | [], [] -> ()
    | x :: xs, y :: ys ->
        if not (Z3.Sort.equal (Z3.Expr.get_sort x) (Z3.Expr.get_sort y)) then
          (eprintf "%s:%s %d: %s@\n" loc inout n m; ok := false);
        f (n + 1) (xs, ys)
    | _ -> (eprintf "%s:%s length mismatch: %s@\n" loc inout m; ok := false) in
  f 0 (xs, ys)

let check_spec ok loc m (args, rets) spec =
  let check_triple t =
    check_sorts_match ok loc "arg" m args t.in_vars;
    check_sorts_match ok loc "ret" m rets t.out_vars in
  TripleSet.iter check_triple spec

let check_proc_specs ok sigs p =
  try
    let s = sigs p.proc_name in
    check_spec ok p.proc_name "spec and proc disagree" s p.proc_spec
  with Not_found -> failwith "sigs should contain p.proc_name (s87q7whe)"

let check_statements ok sigs p =
  let one_call { call_name; call_rets; call_args } =
    try
      let p_params, p_rets = sigs call_name in
      let m = sprintf "bad call to %s" call_name in
      check_sorts_match ok p.proc_name "arg" m p_params call_args;
      check_sorts_match ok p.proc_name "ret" m p_rets call_rets
    with Not_found -> begin
      eprintf "%s called from %s, but not defined@\n" call_name p.proc_name;
      ok := false
    end in
  let one_assignment { asgn_rets; asgn_args; asgn_spec } =
    let loc = sprintf "asgn in %s" p.proc_name in
    check_spec ok loc "sort mismatch" (asgn_args, asgn_rets) asgn_spec in
  let one_statement = function
    | Assignment_core a -> one_assignment a
    | Call_core c -> one_call c
    | _ -> () in
  option () (List.iter one_statement) p.proc_body

(* }}} *)

let check_well_formed q =
  let ok = ref true in
  let sigs = compute_sigs ok q.q_procs in
  List.iter (check_proc_specs ok sigs) q.q_procs;
  List.iter (check_statements ok sigs) q.q_procs;
  if not !ok then raise Not_well_formed

