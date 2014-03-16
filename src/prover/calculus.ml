(* By definition a sequent holds when ((h * f) -> (c * f)) is a valid formula.
NOTE: Any free variable is interpreted as a free variable in the above formula.
For example, if x is free in some of h, f, c, then the sequent is valid when
∀x((h * f) -> (c * f)), because a formula is valid when its closure is valid. *)
type sequent =
  { frame : Z3.Expr.expr
  ; hypothesis : Z3.Expr.expr
  ; conclusion : Z3.Expr.expr }

(*
The subgoal list represents a conjunction.  The goal often has the
form (L*?l |- R*?r): L and R contain the interesting part, while the
pattern variables ?l and ?r capture the rest. The side condition is
a formula that should hold for the rule to fire (it is passed to the
SMT solver, which checks that it is valid).
*)
type rule_schema =
  { schema_name : string (* not essential, just for reporting problems *)
  ; side_condition : Z3.Expr.expr
  ; goal_pattern : sequent
  ; subgoal_pattern : sequent list }

type t = rule_schema list

let sequent_equal { frame = f1; hypothesis = h1; conclusion = c1 }
    { frame = f2; hypothesis = h2; conclusion = c2 } =
  Syntax.expr_equal f1 f2 && Syntax.expr_equal h1 h2 && Syntax.expr_equal c1 c2
