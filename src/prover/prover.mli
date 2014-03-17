open Corestar_std

type frame_and_antiframe =
  { frame : Syntax.expr
  ; antiframe : Syntax.expr }

val is_inconsistent (* The result [false] means "maybe". *)
  : Syntax.context -> Calculus.t -> Syntax.expr -> bool
val is_entailment
  : Syntax.context -> Calculus.t -> Syntax.expr -> Syntax.expr -> bool
val infer_frame (* returned antiframes have the form _x1=E1 * _x2=E2 * ... *)
  : Syntax.context -> Calculus.t -> Syntax.expr -> Syntax.expr -> frame_and_antiframe list
val biabduct
  : Syntax.context -> Calculus.t -> Syntax.expr -> Syntax.expr -> frame_and_antiframe list

(* NOTE: For infer_frame, the empty list result [] means that no suitable
frame was found, while the result [Expression.emp] means that the entailment
holds as given; that is, with an empty frame. Similarly for biabduct. *)

val mk_or
  : Syntax.context -> Syntax.expr -> Syntax.expr -> Syntax.expr
val mk_star
  : Syntax.context -> Syntax.expr -> Syntax.expr -> Syntax.expr
val mk_meet (* [mk_meet a b] is stronger than both [a] and [b] *)
  : Syntax.context -> Syntax.expr -> Syntax.expr -> Syntax.expr
val mk_big_or
  : Syntax.context -> Syntax.expr list -> Syntax.expr
val mk_big_star
  : Syntax.context -> Syntax.expr list -> Syntax.expr
val mk_big_meet
  : Syntax.context -> Syntax.expr list -> Syntax.expr
val normalize
  : Syntax.context -> Syntax.expr -> Syntax.expr

(* For debug only. *)
val print_stats : unit -> unit
