(* Follows SMTLIB2 Section 5.1 (Scripts). *)

type check_sat_response = Sat | Unsat | Unknown

val define_fun : string -> (string * Z3.Sort.sort) list -> Z3.Sort.sort -> Z3.Expr.expr -> unit
val push : unit -> unit
val pop : unit -> unit
val say : Z3.Expr.expr -> unit (** say [e] tells Z3 to assert [e] (assert is a keyword) *)
val check_sat : unit -> check_sat_response

(* For debug. *)
val log_comment : string -> unit
