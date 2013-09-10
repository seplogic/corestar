module Expr = Expression

type frame_and_antiframe =
  { frame : Expr.t
  ; antiframe : Expr.t }

val is_entailment : Expr.t -> Expr.t -> bool
val infer_frame : Expr.t -> Expr.t -> Expr.t list
val biabduct : Expr.t -> Expr.t -> frame_and_antiframe list
