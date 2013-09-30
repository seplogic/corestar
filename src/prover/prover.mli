type frame_and_antiframe =
  { frame : Expression.t
  ; antiframe : Expression.t }

val is_entailment
  : Calculus.t -> Expression.t -> Expression.t -> bool
val infer_frame
  : Calculus.t -> Expression.t -> Expression.t -> Expression.t list
val biabduct
  : Calculus.t -> Expression.t -> Expression.t -> frame_and_antiframe list
