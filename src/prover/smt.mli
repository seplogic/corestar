(* Follows SMTLIB2 Section 5.1 (Scripts). *)

type check_sat_response = Sat | Unsat | Unknown

val define_fun : Syntax.context -> string -> (string * Z3.Sort.sort) list -> Z3.Sort.sort -> Z3.Expr.expr -> unit
val push : Syntax.context -> unit
val pop : Syntax.context -> unit
val say : Syntax.context -> Z3.Expr.expr -> unit (** say [ctx] [e] tells Z3 to assert [e] (assert is a keyword) *)
val check_sat : Syntax.context -> check_sat_response

(* For debug. *)
val log_comment : string -> unit
