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

let pp_expr_list = pp_list_sep "," Syntax.pp_expr

let pp_triple f { pre; post; modifies } =
  fprintf f "@[{%a}@]@,@[(%a)@]@,@[{%a}@]@,"
    Syntax.pp_expr pre
    pp_expr_list modifies
    Syntax.pp_expr post

let pp_spec f ts = pp_list_sep "+" pp_triple f (TripleSet.elements ts)

let pp_subst f (subees, subers) =
  if subees <> [] then
    fprintf f "@[[%a<-%a]@]" pp_expr_list subees pp_expr_list subers
  else ()
let pp_rets_subst f (retf, ret) =
  if retf <> [] then fprintf f "@[returns %a@]" pp_subst (retf, ret)
  else ()

let pp_statement f = function
  | Nop_stmt_core -> fprintf f "nop;"
  | Label_stmt_core l -> fprintf f "label %s;" l
  | Assignment_core { asgn_rets; asgn_rets_formal; asgn_args; asgn_args_formal; asgn_spec } ->
      fprintf f "@[<2>assign@ %a@,%a@,%a;@]"
        pp_spec asgn_spec pp_subst (asgn_args_formal, asgn_args) pp_rets_subst (asgn_rets_formal, asgn_rets)
  | Call_core { call_name; call_rets; call_args } ->
      fprintf f "@[<2>call @[%a@]@,:=@[%s@[(%a)@]@];@]"
        pp_expr_list call_rets call_name pp_expr_list call_args
  | Goto_stmt_core ls ->
      fprintf f "@[goto %a;@]" (pp_list_sep "," pp_string) ls
  | End -> fprintf f "@[end;@]"

let pp_logic _ _ = failwith "TODO (a8d7bnw2w)"

let pp_ast_procedure f { proc_name; proc_spec; proc_body; proc_args; proc_rets } =
  let pp_body f body =
    let pp_nl_core f c = fprintf f "@\n@{<p>%a@}" pp_statement c in
    fprintf f "@\n@[<2>?%a@]" (pp_list pp_nl_core) body in
  fprintf f "@\n@[@{<details>";
  fprintf f "@[<2>@{<summary>procedure %s(%a) returns (%a) :@}@\n%a@]"
    proc_name pp_expr_list proc_args pp_expr_list proc_rets pp_spec proc_spec;
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
  TripleSet.singleton { pre = Syntax.mk_emp; post = f; modifies = [] }
let mk_assert f =
  TripleSet.singleton { pre = f; post = f; modifies = [] }

(* Helpers for [is_well_formed]. *) (* {{{ *)

let compute_sigs ok ps =
  let h = StringHash.create 0 in
  let one_sig p =
    if StringHash.mem h p.proc_name then begin
      eprintf "procedure %s already declared@\n" p.proc_name;
      ok := false
    end;
    StringHash.replace h p.proc_name (p.proc_args, p.proc_rets) in
  List.iter one_sig ps;
  StringHash.find h

(* WARNING: The warning message depends on which of xs&ys is shorter. See also
the comment on [is_well_formed].*)
let check_sorts_match ok loc inout m xs ys =
  let rec f n = function
    | [], [] -> ()
    | x :: xs, y :: ys ->
        if not (Z3.Sort.equal (Z3.Expr.get_sort x) (Z3.Expr.get_sort y)) then
          (eprintf "E:%s:%s %d: %s@\n@?" loc inout n m; ok := false);
        f (n + 1) (xs, ys)
    | xs, [] ->
        eprintf "W:%s:%s: %d ignored %ss@\n@?" loc m (List.length xs) inout
    | [], ys ->
        eprintf "W:%s:%s: %d havocked %ss@\n@?" loc m (List.length ys) inout
  in
  f 0 (xs, ys)

let check_statements ok sigs p =
  let one_call { call_name; call_rets; call_args } =
    try
      let p_args, p_rets = sigs call_name in
      let m = sprintf "bad call to %s" call_name in
      check_sorts_match ok p.proc_name "arg" m call_args p_args;
      check_sorts_match ok p.proc_name "ret" m p_rets call_rets
    with Not_found -> begin
      eprintf "%s called from %s, but not defined@\n" call_name p.proc_name;
      ok := false
    end in
  let one_assignment a =
    let f x = check_sorts_match ok p.proc_name x "assignment" in
    f "arg" a.asgn_args a.asgn_args_formal;
    f "ret" a.asgn_rets_formal a.asgn_rets in
  let one_statement = function
    | Assignment_core a -> one_assignment a
    | Call_core c -> one_call c
    | _ -> () in
  option () (List.iter one_statement) p.proc_body

(* }}} *)

(* Well-formed means that the sorts match at call sites. If the number of
arguments/returns does not match, then the program is still considered
well-formed, but a warning is printed. If the program is not well-formed, an
error is printed.

Here's what happens when the number of arguments/returns is mismatched:
  - more actual arguments -> they get ignored
  - more formal arguments -> they are havocked (uninitialized)
  - more actual returns -> they are havoked
  - more formal returns -> they get ignored *)
(* TODO: check the above for spec/assign statements. *)
let is_well_formed q =
  let ok = ref true in
  let sigs = compute_sigs ok q.q_procs in
  List.iter (check_statements ok sigs) q.q_procs;
  !ok

