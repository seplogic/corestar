type entry =
  | AbstractionRule of Abstraction.rule_schema
  | CalculusRule of Calculus.rule_schema
  | Global of string list
  | Procedure of Core.ast_procedure
