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

open Corestar_std

type var_list = Z3.Expr.expr list
type expr_list = Z3.Expr.expr list

type triple = { pre : Z3.Expr.expr; post : Z3.Expr.expr; modifies : var_list }

module TripleSet = HashSet.Make (struct
  type t = triple

  let equal a b =
    Syntax.expr_equal a.pre b.pre
    && Syntax.expr_equal a.post b.post
    && a.modifies = b.modifies

  let hash { pre; post; modifies } =
    let z3h = Z3.AST.hash @@ Z3.Expr.ast_of_expr in
    Hashtbl.hash (List.map z3h (pre :: post :: modifies))
end)

type spec = TripleSet.t

type rules =
  { calculus : Calculus.t
  ; abstraction : Abstraction.t }

type call =
  { call_name : string
  ; call_rets : var_list
  ; call_args : expr_list }

(* NOTE: Usually [proc_ok] is true, and corestar reports an error when the body
does not refine the specs.  When [proc_ok] is false, corestar reports an error
when the body does refine the specs.  The latter mode is used mostly for
testing. *)
type 'body procedure =
  { proc_name : string
  ; mutable proc_spec : spec
  ; proc_ok : bool
  ; proc_body : 'body option
  ; proc_args : var_list
  ; proc_rets : var_list
  ; proc_rules : rules }

type assignment =
  { asgn_rets : var_list
  ; asgn_rets_formal : var_list
  ; asgn_args : expr_list
  ; asgn_args_formal : var_list
  ; asgn_spec : spec }

type statement =
  | Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of assignment (* TODO: rename to Spec_core *)
  | Call_core of call
  | Goto_stmt_core of string list
  | End

type ast_procedure = statement list procedure

type 'proc question =
  { q_procs : 'proc list
  ; q_globals : var_list (* TODO: remove *)
  ; q_rules : rules
  ; q_infer : bool  (* [true] means do bi-abduction *)
  ; q_name : string }
type ast_question = ast_procedure question
