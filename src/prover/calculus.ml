(* By definition a sequent holds when ((h * f) -> (c * f)) is a valid formula.
NOTE: Any free variable is interpreted as a free variable in the above formula.
For example, if x is free in some of h, f, c, then the sequent is valid when
∀x((h * f) -> (c * f)), because a formula is valid when its closure is valid. *)
type sequent =
  { frame : Z3.Expr.expr
  ; hypothesis : Z3.Expr.expr
  ; conclusion : Z3.Expr.expr }

let rule_num_flags = 4
let rule_no_backtrack = 1 lsl 0
let rule_abduct = 1 lsl 1
let rule_inconsistency = 1 lsl 2
let rule_instantiation = 1 lsl 3

(** default priority for user rules *)
let default_rule_priority = 10000

(** The subgoal list represents a conjunction.

    The goal often has the form (L*?l |- R*?r): L and R contain the
    interesting part, while the pattern variables ?l and ?r capture
    the rest.

    pure_check is a list of pure formulas that should all hold for the
    rule to fire (it is passed to the SMT solver, which checks that
    they are valid).

    fresh_in_expr is a list of pairs (v,e) such that v must not appear
    free in e for the rule to fire.
*)
type sequent_schema =
  { seq_name : string (* not essential, just for reporting problems *)
  ; seq_pure_check : Z3.Expr.expr list
  ; seq_fresh_in_expr : (Z3.Expr.expr * Z3.Expr.expr) list
  ; seq_goal_pattern : sequent
  ; seq_subgoal_pattern : sequent list
  ; seq_priority : int
  ; seq_flags : int }

type rewrite_schema =
  { rw_name : string (* not essential, just for reporting problems *)
  ; rw_from_pattern : Z3.Expr.expr
  ; rw_to_pattern : Z3.Expr.expr }

type rule_schema =
| Sequent_rule of sequent_schema
| Rewrite_rule of rewrite_schema

type t = rule_schema list
