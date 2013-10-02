open Corestar_std

type t

(* the basic constructors *)
val mk_app : string -> t list -> t
val mk_var : string -> t

val bk_app: t -> (string * t list)
val bk_var: t -> string

val freshen : string -> string
  (* [freshen v] is a fresh logical variable whose name is similar to [v].
  NOTE: '#' has a special meaning! See implementation. *)

(* kinds of variables *)
(* Pattern variables:
  ?x matches any expression (formula or term)
  _x matches variables (which are terms) *)
(* Formula variables:
  x is a program variable
  _x is a logical variable *)
val is_pvar : string -> bool (* program variable *)
val is_lvar : string -> bool (* logical variable *)
val is_tpat : string -> bool (* pattern that matches terms *)
val is_vpat : string -> bool (* pattern that matches variables *)

(* operations on formulas *)

val eq : t -> t -> bool
val hash : t -> int
val vars : t -> string list
val substitute : (string * t) list -> t -> t

(* various helpers *)
val mk_0 : string -> t
val mk_1 : string -> t -> t
val mk_2 : string -> t -> t -> t

val nil : t
val emp : t
val fls : t

val mk_star : t -> t -> t
val mk_big_star : t list -> t
val mk_or : t -> t -> t

val mk_eq : t -> t -> t
val mk_neq : t -> t -> t

val mk_string_const : string -> t
val mk_int_const : string -> t

val is_interpreted : string -> bool

val pp : t pretty_printer
