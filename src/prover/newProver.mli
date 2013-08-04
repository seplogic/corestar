type frame_and_antiframe =
  { frame : Formula.t
  ; antiframe : Formula.t }

val is_entailment : Formula.t -> Formula.t -> bool
val infer_frame : Formula.t -> Formula.t -> Formula.t list
val biabduct : Formula.t -> Formula.t -> frame_and_antiframe list
