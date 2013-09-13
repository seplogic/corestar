(* The [concrete_pattern] must match the whole formula that represents the
current state.  As such, it will usually have the form (P * ?f), such that ?f
captures the part of the state we are not abstracting.  Similarly,
[abstract_pattern] produces the whole formula that represents the (abstracted)
state, and usually has the form (Q * ?f).  In general, any pattern variable (_x
or ?x) appearing in [abstract_pattern] must also appear in [concrete_pattern].

TODO: check that patterns are bound in concrete if used in abstract
TODO: add side-conditions (see where clauses in examples)
*)
type rule_schema =
  { concrete_pattern : Expression.t
  ; abstract_pattern : Expression.t }


type t = rule_schema list
