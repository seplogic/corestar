(* By definition a sequent holds when ((h * f) -> (c * f)) is a valid formula.
NOTE: Any free variable is interpreted as a free variable in the above formula.
For example, if x is free in some of h, f, c, then the sequent is valid when
∀x((h * f) -> (c * f)), because a formula is valid when its closure is valid. *)
type sequent =
  { frame : Z3.Expr.expr
  ; hypothesis : Z3.Expr.expr
  ; conclusion : Z3.Expr.expr }

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
type rule_schema =
  { schema_name : string (* not essential, just for reporting problems *)
  ; pure_check : Z3.Expr.expr list
  ; fresh_in_expr : (Z3.Expr.expr * Z3.Expr.expr) list
  ; goal_pattern : sequent
  ; subgoal_pattern : sequent list }

type t = rule_schema list

let sequent_equal { frame = f1; hypothesis = h1; conclusion = c1 }
    { frame = f2; hypothesis = h2; conclusion = c2 } =
  Syntax.expr_equal f1 f2 && Syntax.expr_equal h1 h2 && Syntax.expr_equal c1 c2
