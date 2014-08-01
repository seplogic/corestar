open Calculus
open Corestar_std
open Format

let sequent_equal { frame = f1; hypothesis = h1; conclusion = c1 }
    { frame = f2; hypothesis = h2; conclusion = c2 } =
  Syntax.expr_equal f1 f2 && Syntax.expr_equal h1 h2 && Syntax.expr_equal c1 c2

let is_abduct_rule f = f land rule_abduct <> 0
let is_inconsistency_rule f = f land rule_inconsistency <> 0
let is_no_backtrack_rule f = f land rule_no_backtrack <> 0
let is_instantiation_rule f = f land rule_instantiation <> 0

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

let mk_equiv_rule name priority flags lhs rhs =
  let f = Syntax.mk_fresh_bool_tpat "_f" in
  let lo = Syntax.mk_fresh_bool_tpat "_lo" in
  let rs =
    [{ seq_name = name ^ "_right"
     ; seq_pure_check = []
     ; seq_fresh_in_expr = []
     ; seq_goal_pattern = { frame = f; hypothesis = lo; conclusion = lhs }
     ; seq_subgoal_pattern = [{ frame = f; hypothesis = lo; conclusion = rhs }]
     ; seq_priority = priority
     ; seq_flags = flags };
     { seq_name = name ^ "_left"
     ; seq_pure_check = []
     ; seq_fresh_in_expr = []
     ; seq_goal_pattern = { frame = f; hypothesis = lhs; conclusion = lo }
     ; seq_subgoal_pattern = [{ frame = f; hypothesis = rhs; conclusion = lo }]
     ; seq_priority = priority
     ; seq_flags = flags }] in
  List.map (fun r -> Sequent_rule r) rs

let (++) = Syntax.ExprSet.union
let union_map f = List.fold_left (fun s x -> f x ++ s) Syntax.ExprSet.empty
let union_pair_map f (a, b) = f a ++ f b

let vars_of_sequent { frame; hypothesis; conclusion } =
  Syntax.vars frame ++ Syntax.vars hypothesis ++ Syntax.vars conclusion

let vars_of_sequent_schema
      { seq_name; seq_pure_check; seq_fresh_in_expr; seq_goal_pattern
        ; seq_subgoal_pattern; seq_priority; seq_flags } =
  let v = Syntax.vars in
  union_map v seq_pure_check
  ++ union_map (union_pair_map v) seq_fresh_in_expr
  ++ vars_of_sequent seq_goal_pattern
  ++ union_map vars_of_sequent seq_subgoal_pattern

let vars_of_rewrite_schema { rw_name; rw_from_pattern; rw_to_pattern } =
  Syntax.vars rw_from_pattern ++ Syntax.vars rw_to_pattern

let vars_of_rule_schema = function
  | Sequent_rule r -> vars_of_sequent_schema r
  | Rewrite_rule r -> vars_of_rewrite_schema r

let subst_in_sequent subst { frame; hypothesis; conclusion } =
  { frame = subst frame
  ; hypothesis = subst hypothesis
  ; conclusion = subst conclusion }

let subst_in_sequent_schema subst r =
  { r with
    seq_pure_check = List.map subst r.seq_pure_check
  ; seq_fresh_in_expr = List.map (pair_map subst) r.seq_fresh_in_expr
  ; seq_goal_pattern = subst_in_sequent subst r.seq_goal_pattern
  ; seq_subgoal_pattern = List.map (subst_in_sequent subst) r.seq_subgoal_pattern }

let subst_in_rewrite_schema subst r =
  { r with
    rw_from_pattern = subst r.rw_from_pattern
    ; rw_to_pattern = subst r.rw_to_pattern }

let subst_in_rule_schema subst = function
  | Sequent_rule r -> Sequent_rule (subst_in_sequent_schema subst r)
  | Rewrite_rule r -> Rewrite_rule (subst_in_rewrite_schema subst r)

(* well-formedness checks:
  - pattern variables occuring in subgoals also occur in goal
  - TODO: if ?x patterns (for formulas and terms) don't mix up formulas and terms
    (Jules: I don't understand this one. Is it still relevant?)
 *)
(* {{{ *)

let filter_pats =
  Syntax.ExprSet.filter (fun e -> Syntax.is_tpat e || Syntax.is_vpat e)

let check_sequent_schema r =
  let gps = filter_pats (vars_of_sequent r.seq_goal_pattern) in
  let sgps = union_map (filter_pats @@ vars_of_sequent) r.seq_subgoal_pattern in
  let b = Syntax.ExprSet.subset sgps gps in
  if not b then (
    let ps = Syntax.ExprSet.diff sgps gps in
    eprintf
      "pattern(s) %a appear in the subgoals of rule %s but not in the goal.@\n"
      (pp_list Syntax.pp_expr) (Syntax.ExprSet.elements ps) r.seq_name);
  b

let check_rewrite_schema r =
  let pats_of = filter_pats @@ Syntax.vars in
  let b = Syntax.ExprSet.subset (pats_of r.rw_to_pattern)
                                (pats_of r.rw_from_pattern) in
  if not b then (
    let ps = Syntax.ExprSet.diff (pats_of r.rw_to_pattern)
                                 (pats_of r.rw_from_pattern) in
    eprintf
      "pattern(s) %a appear in the RHS of rule %s but not in the LHS.@\n"
      (pp_list Syntax.pp_expr) (Syntax.ExprSet.elements ps) r.rw_name);
  b

let check_rule_schema = function
  | Sequent_rule r -> check_sequent_schema r
  | Rewrite_rule r -> check_rewrite_schema r

let check_calculus = List.for_all check_rule_schema
