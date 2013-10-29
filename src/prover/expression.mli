open Corestar_std

type t

(* TODO: Make these opaque? *)
type var = string
type op = string
type sort = string

(* sorts (aka types) *)
val declare_sort : sort -> unit
val declare_op : op -> sort list -> sort -> unit
val sort_of : t -> sort

(* the basic constructors *)
val mk_app : op -> t list -> t
val mk_var : var -> t

val bk_app : t -> (op * t list)
val bk_var : t -> var

val freshen : var -> var
  (* [freshen v] is a fresh logical variable whose name is similar to [v].
  NOTE: '#' has a special meaning! See implementation. *)

(* kinds of variables *)
(* Pattern variables:
  ?x matches any expression (formula or term)
  _x matches variables (which are terms) *)
(* Formula variables:
  x is a program variable
  _x is a logical variable *)
val is_pvar : var -> bool (* program variable *)
val is_lvar : var -> bool (* logical variable *)
val is_tpat : var -> bool (* pattern that matches terms or formulas *)
val is_vpat : var -> bool (* pattern that matches variables *)

(* operations on formulas *)

val equal : t -> t -> bool
val hash : t -> int
val size : t -> int
val vars : t -> var list
val substitute : (var * t) list -> t -> t

(* various helpers *)
val mk_0 : op -> t
val mk_1 : op -> t -> t
val mk_2 : op -> t -> t -> t

val nil : t
val emp : t
val fls : t

val mk_star : t -> t -> t
val mk_big_star : t list -> t
val mk_or : t -> t -> t
val mk_big_or : t list -> t

val mk_eq : t -> t -> t
val mk_neq : t -> t -> t

val mk_string_const : string -> t
val mk_int_const : string -> t

(* [on_star f g op xs] returns either [f xs] or [g op xs] depending on whether
[op] is a star or not. Similarly for the other [on_*] functions. In other
modules, you should prefer to use these together with [cases] instead of
mentioning strings. *)
val cases : (var -> 'a) -> (op -> t list -> 'a) -> t -> 'a
type 'a app_eval = (op -> t list -> 'a) -> (op -> t list -> 'a)
type 'a app_eval_n = (t list -> 'a) -> 'a app_eval
type 'a app_eval_2 = (t -> t -> 'a) -> 'a app_eval
val on_star : 'a app_eval_n
val on_or : 'a app_eval_n
val on_eq : 'a app_eval_2
val on_neq : 'a app_eval_2

val is_interpreted : string -> bool

val pp : t pretty_printer
