module Expr = Expression

(* By definition a sequent holds when ((h * f) -> (c * f)) is a valid formula.
NOTE: Any free variable is interpreted as a free variable in the above formula.
For example, if x is free in some of h, f, c, then the sequent is valid when
∀x((h * f) -> (c * f)), because a formula is valid when its closure is valid. *)
type sequent =
  { frame : Expr.t
  ; hypothesis : Expr.t
  ; conclusion : Expr.t }

(*
The subgoal may use conjunctions and disjunctions.  The goal and the subgoal may
contain pattern variables (?x matches any term, _x matches only variables).  All
pattern variables appearing in the subgoal must also appear in the goal. A rule
is obtained from the rule schema by instantiating all pattern variables with
some terms.
NOTE: It is often the case that [goal_pattern] has the form (g * _f), and the
[subgoal_pattern] has the form (s * _f) or ((s1 * _f) ∧ ... ∧ (sn * _f)), where
_f is a pattern variable.
TODO: Such assumptions about the shape must be captured by functions with the
type [rule_schema -> bool].
 *)
type rule_schema =
  { goal_pattern : sequent
  ; subgoal_pattern : sequent }
