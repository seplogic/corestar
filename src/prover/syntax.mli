open Corestar_std

type context
type var = string
type expr = Z3.Expr.expr
type func_decl = Z3.FuncDecl.func_decl

val mk_context : unit -> context
val z3_context : context -> Z3.context
val z3_solver : context -> Z3.Solver.solver

(* string operations *)
val mk_string_const : context -> string -> expr (* with side-effects! *)
val string_sort : context -> Z3.Sort.sort
val get_all_string_exprs : unit -> expr list

(* an omission from Z3's ocaml binding *)
val expr_compare : expr -> expr -> int
val expr_equal : expr -> expr -> bool

module HashableExpr : Hashtbl.HashedType with type t = expr
module ExprSet : Set.S with type elt = expr
module ExprMap : Map.S with type key = expr
module ExprHashSet : HashSet.S with type elt = expr
module ExprHashMap : Hashtbl.S with type key = expr

val freshen : context -> expr -> expr
  (* [freshen v] is a fresh logical variable whose name is similar to [v].
  NOTE: '!' has a special meaning! See implementation. *)

(* kinds of variables *)
(* Pattern variables:
  ?x matches any expression (formula or term)
  _x matches variables (which are terms) *)
(* Formula variables:
  x is a program variable
  _x is a logical variable *)
val is_pvar_name : var -> bool (* program variable *)
val is_global_name : var -> bool (* global variables *)
val is_lvar_name : var -> bool (* logical variable *)
val is_tpat_name : var -> bool (* pattern that matches terms or formulas *)
val is_vpat_name : var -> bool (* pattern that matches variables *)
val is_pvar : expr -> bool
val is_global : expr -> bool (* to deprecate *)
val is_lvar : expr -> bool
val is_tpat : expr -> bool
val is_vpat : expr -> bool

(* Predicates are pure if they start with "!". *)
val is_pure : context -> expr -> bool

(* operations on formulas *)
val size : expr -> int
val vars : expr -> expr list

(* various helpers *)
val mk_0 : context -> string -> expr
val mk_1 : func_decl -> expr -> expr
val mk_2 : func_decl -> expr -> expr -> expr

val emp : context -> func_decl
val star : context -> func_decl

val mk_pvar : context -> var -> expr
val mk_gvar : context -> var -> expr
val mk_lvar : context -> var -> expr

val mk_big_star : context -> expr list -> expr
val mk_big_or : context -> expr list -> expr
val mk_emp : context -> expr
val mk_eq : context -> expr -> expr -> expr
val mk_distinct : context -> expr list -> expr
val mk_not :context -> expr -> expr
val mk_or : context -> expr -> expr -> expr
val mk_star : context -> expr -> expr -> expr
val mk_false : context -> expr


(* [on_star f g op xs] returns either [f xs] or [g op xs] depending on
   whether [op] is a star or not. Similarly for the other [on_*]
   functions. In other modules, you should prefer to use these instead of
   mentioning strings. *)
type 'a app_eval = (expr -> 'a) -> (expr -> 'a)
type 'a app_eval_0 = (unit -> 'a) -> 'a app_eval
type 'a app_eval_1 = (expr -> 'a) -> 'a app_eval
type 'a app_eval_2 = (expr -> expr -> 'a) -> 'a app_eval
type 'a app_eval_n = (expr list -> 'a) -> 'a app_eval
val on_const : (expr -> 'a) -> 'a app_eval
val on_var : (expr -> 'a) -> 'a app_eval
val on_app : (func_decl -> expr list -> 'a) -> expr -> 'a
val on_emp : context -> 'a app_eval_0
val on_eq : 'a app_eval_2
val on_false : 'a app_eval_0
val on_distinct : 'a app_eval_n
val on_not : 'a app_eval_1
val on_or : 'a app_eval_n
val on_star : context -> 'a app_eval_2
(** if [e] is of the form "e1 * (e2 * (... * en))" where en is not
    itself of the form "en' * en''", call [f] on the list [e1; e2; ...;
    en] *)
val on_big_star : context -> 'a app_eval_n
val on_string_const : context -> (string -> 'a) -> 'a app_eval
val on_int_const : context -> (int -> 'a) -> 'a app_eval
val on_op : func_decl -> 'a app_eval_n

(* Example: let rec f e = cases (fun _->false) (recurse f) *)
val recurse : (expr -> expr) -> (func_decl -> expr list -> expr)
val pp_expr : expr pretty_printer
