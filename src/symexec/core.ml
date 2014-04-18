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

type args_out = Z3.Expr.expr list
type args_in = Z3.Expr.expr list

type triple = { pre : Z3.Expr.expr; post : Z3.Expr.expr;
		in_vars : args_in; out_vars : args_in;
		modifies : args_out }

module TripleSet = HashSet.Make (struct
  type t = triple

  let equal a b =
    Syntax.expr_equal a.pre b.pre
    && Syntax.expr_equal a.post b.post
    && a.in_vars = b.in_vars
    && a.out_vars = b.out_vars
    && a.modifies = b.modifies

  let hash { pre; post; in_vars; out_vars; modifies } =
    ((Z3.AST.hash (Z3.Expr.ast_of_expr pre) * 31) + Z3.AST.hash (Z3.Expr.ast_of_expr post)) * 31 + Hashtbl.hash in_vars + Hashtbl.hash out_vars + Hashtbl.hash modifies
end)

type spec = TripleSet.t

type rules =
  { calculus : Calculus.t
  ; abstraction : Abstraction.t }

type call =
  { call_name : string
  ; call_rets : args_out
  ; call_args : args_in }

(* NOTE: Usually [proc_ok] is true, and corestar reports an error when the body
does not refine the specs.  When [proc_ok] is false, corestar reports an error
when the body does refine the specs.  The latter mode is used mostly for
testing. *)
type 'body procedure =
  { proc_name : string
  ; mutable proc_spec : spec
  ; proc_ok : bool
  ; proc_body : 'body option
  ; proc_params : Z3.Expr.expr list
  ; proc_rets : Z3.Expr.expr list
  ; proc_rules : rules }

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
  ; q_globals : Z3.Expr.expr list
  ; q_rules : rules
  ; q_infer : bool  (* [true] means do bi-abduction *)
  ; q_name : string }
type ast_question = ast_procedure question
