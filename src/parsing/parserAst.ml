type entry =
  | ProverQuery of Psyntax.question
  | Rule of Psyntax.rules
  | Procedure of Core.ast_procedure
