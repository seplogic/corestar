(* Follows SMTLIB2 Section 5.1 (Scripts). *)

type sort = Expression.sort
type symbol = Expression.op
type term = Expression.t
type var = Expression.var

type check_sat_response = Sat | Unsat | Unknown

val define_fun : symbol -> (var * sort) list -> sort -> term -> unit
val push : unit -> unit
val pop : unit -> unit
val say : term -> unit (* instead of ‘assert’, which is a keyword *)
val check_sat : unit -> check_sat_response

(* For debug. *)
val log_comment : string -> unit
val close_log : unit -> unit

