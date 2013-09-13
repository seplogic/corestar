type entry =
  | AbstractionRule of Abstraction.rule_schema
  | CalculusRule of Calculus.rule_schema
  | Procedure of Core.ast_procedure
