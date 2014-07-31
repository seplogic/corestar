open Calculus
open Corestar_std

val sequent_equal : sequent -> sequent -> bool

val is_abduct_rule : int -> bool
val is_inconsistency_rule : int -> bool
val is_no_backtrack_rule : int -> bool
val is_instantiation_rule : int -> bool

val is_rule_schema_ok : rule_schema -> bool

val mk_equiv_rule : string -> int -> int -> Z3.Expr.expr -> Z3.Expr.expr -> t

val pp_sequent : sequent pretty_printer
val pp_rule_schema : rule_schema pretty_printer
