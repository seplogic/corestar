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

let is_abduct_rule f = f land rule_abduct <> 0
let is_inconsistency_rule f = f land rule_inconsistency <> 0
let is_no_backtrack_rule f = f land rule_no_backtrack <> 0
let is_instantiation_rule f = f land rule_instantiation <> 0

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
type rule_schema =
  { schema_name : string (* not essential, just for reporting problems *)
  ; pure_check : Z3.Expr.expr list
  ; fresh_in_expr : (Z3.Expr.expr * Z3.Expr.expr) list
  ; goal_pattern : sequent
  ; subgoal_pattern : sequent list
  ; rule_priority : int
  ; rule_flags : int }

type t = rule_schema list

let mk_equiv_rule name priority flags lhs rhs =
  let f = Syntax.mk_fresh_bool_tpat "_f" in
  let lo = Syntax.mk_fresh_bool_tpat "_lo" in
  [{ schema_name = name ^ "_right"
   ; pure_check = []
   ; fresh_in_expr = []
   ; goal_pattern = { frame = f; hypothesis = lo; conclusion = lhs }
   ; subgoal_pattern = [{ frame = f; hypothesis = lo; conclusion = rhs }]
   ; rule_priority = priority
   ; rule_flags = flags };
   { schema_name = name ^ "_left"
   ; pure_check = []
   ; fresh_in_expr = []
   ; goal_pattern = { frame = f; hypothesis = lhs; conclusion = lo }
   ; subgoal_pattern = [{ frame = f; hypothesis = rhs; conclusion = lo }]
   ; rule_priority = priority
   ; rule_flags = flags }]

let sequent_equal { frame = f1; hypothesis = h1; conclusion = c1 }
    { frame = f2; hypothesis = h2; conclusion = c2 } =
  Syntax.expr_equal f1 f2 && Syntax.expr_equal h1 h2 && Syntax.expr_equal c1 c2
