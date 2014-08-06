open Calculus
open Corestar_std

val sequent_equal : sequent -> sequent -> bool

val is_abduct_rule : int -> bool
val is_inconsistency_rule : int -> bool
val is_no_backtrack_rule : int -> bool
val is_instantiation_rule : int -> bool

val check_rule_schema : rule_schema -> bool
val check_calculus : t -> bool

val vars_of_sequent : sequent -> Syntax.ExprSet.t
val vars_of_sequent_schema : sequent_schema -> Syntax.ExprSet.t
val vars_of_rewrite_schema : rewrite_schema -> Syntax.ExprSet.t
val vars_of_rule_schema : rule_schema -> Syntax.ExprSet.t
val subst_in_sequent : (Z3.Expr.expr -> Z3.Expr.expr) -> sequent -> sequent
val subst_in_sequent_schema : (Z3.Expr.expr -> Z3.Expr.expr) -> sequent_schema -> sequent_schema
val subst_in_rewrite_schema : (Z3.Expr.expr -> Z3.Expr.expr) -> rewrite_schema -> rewrite_schema
val subst_in_rule_schema : (Z3.Expr.expr -> Z3.Expr.expr) -> rule_schema -> rule_schema

val pp_sequent : sequent pretty_printer
val pp_rule_schema : rule_schema pretty_printer
