open Corestar_std

type frame_and_antiframe =
  { frame : Z3.Expr.expr
  ; antiframe : Z3.Expr.expr }

val is_inconsistent (* The result [false] means "maybe". *)
  : Calculus.t -> Z3.Expr.expr -> bool
val is_entailment
  : Calculus.t -> Z3.Expr.expr -> Z3.Expr.expr -> bool
val infer_frame (* returned antiframes have the form _x1=E1 * _x2=E2 * ... *)
  : Calculus.t -> Z3.Expr.expr -> Z3.Expr.expr -> frame_and_antiframe list
val biabduct
  : Calculus.t -> Z3.Expr.expr -> Z3.Expr.expr -> frame_and_antiframe list

(* NOTE: For infer_frame, the empty list result [] means that no suitable
frame was found, while the result [Expression.emp] means that the entailment
holds as given; that is, with an empty frame. Similarly for biabduct. *)

val mk_or
  : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_star
  : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_meet (* [mk_meet a b] is stronger than both [a] and [b] *)
  : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_big_or
  : Z3.Expr.expr list -> Z3.Expr.expr
val mk_big_star
  : Z3.Expr.expr list -> Z3.Expr.expr
val mk_big_meet
  : Z3.Expr.expr list -> Z3.Expr.expr
val normalize
  : Z3.Expr.expr -> Z3.Expr.expr

val rewrite_in_expr : Z3.Expr.expr list -> Calculus.rewrite_schema -> Z3.Expr.expr -> Z3.Expr.expr

(* For debug only. *)
val print_stats : unit -> unit
