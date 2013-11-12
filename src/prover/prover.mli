type frame_and_antiframe =
  { frame : Expression.t
  ; antiframe : Expression.t }

val is_inconsistent (* The result [false] means "maybe". *)
  : Calculus.t -> Expression.t -> bool
val is_entailment
  : Calculus.t -> Expression.t -> Expression.t -> bool
val infer_frame
  : Calculus.t -> Expression.t -> Expression.t -> Expression.t list
val biabduct
  : Calculus.t -> Expression.t -> Expression.t -> frame_and_antiframe list

(* NOTE: For infer_frame, the empty list result [] means that no suitable
frame was found, while the result [Expression.emp] means that the entailment
holds as given; that is, with an empty frame. Similarly for biabduct. *)

val mk_big_star
  : Expression.t list -> Expression.t
val mk_star
  : Expression.t -> Expression.t -> Expression.t
val normalize
  : Expression.t -> Expression.t
