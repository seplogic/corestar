open Corestar_std

type t

type symbol = string
type var = symbol
type op = symbol
type sort = string

(* sorts (aka types) *)
val declare_sort : sort -> unit
val declare_symbol : symbol -> (sort list * sort) -> unit
val sort_of : t -> (sort list * sort)

(* the basic constructors *)
val mk_app : op -> t list -> t
val mk_var : var -> t

val bk_app : t -> (op * t list)
val bk_var : t -> var

val freshen : var -> var
  (* [freshen v] is a fresh logical variable whose name is similar to [v].
  NOTE: '#' has a special meaning! See implementation. *)

val fresh_pvar : string -> var

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

(* Predicates are pure if the star with "!". *)
val is_pure : t -> bool

(* operations on formulas *)

val equal : t -> t -> bool
val hash : t -> int
val size : t -> int
val vars : t -> var list
val substitute_gen : (t * t) list -> t -> t
val substitute : (var * t) list -> t -> t

(* various helpers *)
val mk_0 : op -> t
val mk_1 : op -> t -> t
val mk_2 : op -> t -> t -> t

val emp : t
val fls : t

val mk_star : t -> t -> t
val mk_big_star : t list -> t
val mk_or : t -> t -> t
val mk_big_or : t list -> t

val mk_not : t -> t

val mk_eq : t -> t -> t
val mk_neq : t -> t -> t

val mk_string_const : string -> t
val mk_int_const : string -> t

(* [on_star f g op xs] returns either [f xs] or [g op xs] depending on whether
[op] is a star or not. Similarly for the other [on_*] functions. In other
modules, you should prefer to use these together with [cases] instead of
mentioning strings. ([match_] is the same as [cases], except for argument
order.)  *)
val cases : (var -> 'a) -> (op -> t list -> 'a) -> t -> 'a
val match_ : t -> (var -> 'a) -> (op -> t list -> 'a) -> 'a
type 'a app_eval = (op -> t list -> 'a) -> (op -> t list -> 'a)
type 'a app_eval_0 = (unit -> 'a) -> 'a app_eval
type 'a app_eval_1 = (t -> 'a) -> 'a app_eval
type 'a app_eval_2 = (t -> t -> 'a) -> 'a app_eval
type 'a app_eval_n = (t list -> 'a) -> 'a app_eval
val on_emp : 'a app_eval_0
val on_fls : 'a app_eval_0
val on_star : 'a app_eval_n
val on_or : 'a app_eval_n
val on_not : 'a app_eval_1
val on_eq : 'a app_eval_2
val on_neq : 'a app_eval_2
val on_string_const : (string -> 'a) -> 'a app_eval
val on_int_const : (string -> 'a) -> 'a app_eval
val on_op : op -> 'a app_eval_n

(* Example: let rec f e = cases (fun _->false) (recurse f) *)
val recurse : (t -> t) -> (op -> t list -> t)

val pp : t pretty_printer


(* HACK. To remove. *)
val stem : var -> var
