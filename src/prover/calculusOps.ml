open Calculus
open Corestar_std
open Format

(* Checks:
  - if pattern variables occuring in subgoals also occur in goal
  - if ?x patterns (for formulas and terms) don't mix up formulas and terms
 *)
let is_rule_schema_ok _ = failwith "TODO: CalculusOps.is_rule_schema_ok"

let pp_sequent f { frame; hypothesis; conclusion } =
  fprintf f "@[<2>@[%a@]@ | @[%a@]@ ⊢ @[%a@]@]"
    Syntax.pp_expr frame Syntax.pp_expr hypothesis Syntax.pp_expr conclusion

(* TODO: pp side conditions/priority/flags *)
let pp_seq_schema f { seq_name; seq_goal_pattern; seq_subgoal_pattern } =
  fprintf f "@[<2>rule %s:@ @[%a@]@ if @[%a@];@]@\n"
    seq_name
    pp_sequent seq_goal_pattern
    (pp_list_sep ", " pp_sequent) seq_subgoal_pattern

(* TODO: pp priority/flags *)
let pp_rw_schema f { rw_name; rw_from_pattern; rw_to_pattern } =
  fprintf f "@[<2>rule %s:@ @[%a@]@ ~~> @[%a@];@]@\n"
    rw_name
    Syntax.pp_expr rw_from_pattern
    Syntax.pp_expr rw_to_pattern

let pp_rule_schema f = function
  | Sequent_rule r -> pp_seq_schema f r
  | Rewrite_rule r -> pp_rw_schema f r
