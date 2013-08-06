open Corestar_std

type t

(* the basic constructors *)
val mk_app : string -> t list -> t
val mk_var : string -> t

(* operations on formulas *)

val eq : t -> t -> bool
val hash : t -> int

(* various helpers *)
val mk_0 : string -> t
val mk_1 : string -> t -> t
val mk_2 : string -> t -> t -> t

val emp : t
val fls : t

val mk_star : t -> t -> t
val mk_big_star : t list -> t
val mk_or : t -> t -> t

val mk_eq : t -> t -> t

val mk_string_const : string -> t
val mk_int_const : string -> t

val is_interpreted : string -> bool

val pp : t pretty_printer
