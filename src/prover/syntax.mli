open Corestar_std

type var = string

(** the global Z3 context *)
val z3_ctx : Z3.context

(* string operations *)
val mk_string_const : string -> Z3.Expr.expr (* with side-effects! *)
val string_sort : Z3.Sort.sort
val get_all_string_exprs : unit -> Z3.Expr.expr list

(* an omission from Z3's ocaml binding *)
val expr_compare : Z3.Expr.expr -> Z3.Expr.expr -> int
val expr_equal : Z3.Expr.expr -> Z3.Expr.expr -> bool

module HashableExpr : Hashtbl.HashedType with type t = Z3.Expr.expr
module ExprSet : Set.S with type elt = Z3.Expr.expr
module ExprMap : Map.S with type key = Z3.Expr.expr
module ExprHashSet : HashSet.S with type elt = Z3.Expr.expr
module ExprHashMap : Hashtbl.S with type key = Z3.Expr.expr

val freshen : Z3.Expr.expr -> Z3.Expr.expr
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
val is_pvar : Z3.Expr.expr -> bool
val is_global : Z3.Expr.expr -> bool (* to deprecate *)
val is_lvar : Z3.Expr.expr -> bool
val is_tpat : Z3.Expr.expr -> bool
val is_vpat : Z3.Expr.expr -> bool

(* Predicates are pure if the star with "!". *)
val is_pure : Z3.Expr.expr -> bool

(* operations on formulas *)
val size : Z3.Expr.expr -> int
val vars : Z3.Expr.expr -> Z3.Expr.expr list

(* various helpers *)
val mk_0 : string -> Z3.Expr.expr
val mk_1 : Z3.FuncDecl.func_decl -> Z3.Expr.expr -> Z3.Expr.expr
val mk_2 : Z3.FuncDecl.func_decl -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val emp : Z3.FuncDecl.func_decl
val star : Z3.FuncDecl.func_decl

val mk_pvar : var -> Z3.Expr.expr
val mk_gvar : var -> Z3.Expr.expr
val mk_lvar : var -> Z3.Expr.expr

val mk_big_star : Z3.Expr.expr list -> Z3.Expr.expr
val mk_emp : Z3.Expr.expr
val mk_eq : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_not :Z3.Expr.expr -> Z3.Expr.expr
val mk_or : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_star : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

(* [on_star f g op xs] returns either [f xs] or [g op xs] depending on
   whether [op] is a star or not. Similarly for the other [on_*]
   functions. In other modules, you should prefer to use these instead of
   mentioning strings. *)
(* [match_] is the same as [cases], except for argument
   order. *)
type 'a app_eval = (Z3.Expr.expr -> 'a) -> (Z3.Expr.expr -> 'a)
type 'a app_eval_0 = (unit -> 'a) -> 'a app_eval
type 'a app_eval_1 = (Z3.Expr.expr -> 'a) -> 'a app_eval
type 'a app_eval_2 = (Z3.Expr.expr -> Z3.Expr.expr -> 'a) -> 'a app_eval
type 'a app_eval_n = (Z3.Expr.expr list -> 'a) -> 'a app_eval
val on_const : (Z3.Expr.expr -> 'a) -> 'a app_eval
val on_var : (Z3.Expr.expr -> 'a) -> 'a app_eval
val on_app : (Z3.FuncDecl.func_decl -> Z3.Expr.expr list -> 'a) -> Z3.Expr.expr -> 'a
val on_emp : 'a app_eval_0
val on_eq : 'a app_eval_2
val on_false : 'a app_eval_0
val on_distinct : 'a app_eval_n
val on_not : 'a app_eval_1
val on_or : 'a app_eval_n
val on_star : 'a app_eval_2
(** if [e] is of the form "e1 * (e2 * (... * en))" where en is not
    itself of the form "en' * en''", call [f] on the list [e1; e2; ...;
    en] *)
val on_big_star : 'a app_eval_n
val on_string_const : (string -> 'a) -> 'a app_eval
val on_int_const : (int -> 'a) -> 'a app_eval
val on_op : Z3.FuncDecl.func_decl -> 'a app_eval_n

(* Example: let rec f e = cases (fun _->false) (recurse f) *)
val recurse : (Z3.Expr.expr -> Z3.Expr.expr) -> (Z3.FuncDecl.func_decl -> Z3.Expr.expr list -> Z3.Expr.expr)
val pp_expr : Z3.Expr.expr pretty_printer
