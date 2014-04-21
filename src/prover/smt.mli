(* Follows SMTLIB2 Section 5.1 (Scripts). *)

type check_sat_response = Sat | Unsat | Unknown

val push : unit -> unit
val pop : unit -> unit
val say : Z3.Expr.expr -> unit (** say [e] tells Z3 to assert [e] (assert is a keyword) *)
val check_sat : unit -> check_sat_response
  (* NOTE: [check_sat] does some magic related to '*'. If all the assertions on
  the stack are pure, then Z3 is informed that '*' is the same as 'and'.
  Otherwise, '*' remains uninterpreted, and it is the job of the client to
  provide an axiomatization for it. *)

val print_stats : unit -> unit
val dump_solver : unit -> unit
