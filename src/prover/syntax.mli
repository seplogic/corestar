open Corestar_std

(* TODO: We want mk_star, mk_big_star, mk_or, mk_big_or here.
We don't want on_big_star here because it's slow; but we have one in Prover. *)

type var

(** the global Z3 context *)
val z3_ctx : Z3.context

(* int operations *) (* TODO: Not clear if we want these here. *)
val int_sort : Z3.Sort.sort
val mk_int_const : string -> Z3.Expr.expr
val mk_int_plvar : string -> Z3.Expr.expr
val mk_int_pgvar : string -> Z3.Expr.expr
val mk_int_lvar : string -> Z3.Expr.expr
val mk_int_tpat : string -> Z3.Expr.expr
val mk_int_vpat : string -> Z3.Expr.expr

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
val is_pvar_name : var -> bool (* program variable *)
val is_plvar_name : var -> bool (* program local variable *)
val is_pgvar_name : var -> bool (* program global variables *)
val is_lvar_name : var -> bool (* logical variable *)
val is_tpat_name : var -> bool (* pattern that matches terms or formulas *)
val is_vpat_name : var -> bool (* pattern that matches variables *)
val is_pvar : Z3.Expr.expr -> bool
val is_plvar : Z3.Expr.expr -> bool
val is_pgvar : Z3.Expr.expr -> bool
val is_lvar : Z3.Expr.expr -> bool
val is_tpat : Z3.Expr.expr -> bool
val is_vpat : Z3.Expr.expr -> bool
val var_name : var -> string

(* Predicates are pure if they start with "!". *)
(* formula variables are considered impure *)
val is_pure : Z3.Expr.expr -> bool

(* operations on formulas *)
val size : Z3.Expr.expr -> int
val vars : Z3.Expr.expr -> Z3.Expr.expr list

(* various helpers *)
val mk_0 : string -> Z3.Expr.expr
val mk_1 : Z3.FuncDecl.func_decl -> Z3.Expr.expr -> Z3.Expr.expr
val mk_2 : Z3.FuncDecl.func_decl -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_n : Z3.FuncDecl.func_decl -> Z3.Expr.expr list -> Z3.Expr.expr

val emp : Z3.FuncDecl.func_decl
val star : Z3.FuncDecl.func_decl

val mk_plvar : Z3.Sort.sort -> string -> Z3.Expr.expr
val mk_pgvar : Z3.Sort.sort -> string -> Z3.Expr.expr
val mk_lvar : Z3.Sort.sort -> string -> Z3.Expr.expr
val mk_tpat : Z3.Sort.sort -> string -> Z3.Expr.expr
val mk_vpat : Z3.Sort.sort -> string -> Z3.Expr.expr
val mk_fresh_lvar : Z3.Sort.sort -> string -> Z3.Expr.expr

val bool_sort : Z3.Sort.sort
val mk_bool_plvar : string -> Z3.Expr.expr
val mk_bool_pgvar : string -> Z3.Expr.expr
val mk_bool_lvar : string -> Z3.Expr.expr
val mk_bool_tpat : string -> Z3.Expr.expr
val mk_bool_vpat : string -> Z3.Expr.expr

val mk_big_star : Z3.Expr.expr list -> Z3.Expr.expr
val mk_distinct : Z3.Expr.expr list -> Z3.Expr.expr
val mk_emp : Z3.Expr.expr
val mk_eq : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_false : Z3.Expr.expr
val mk_not :Z3.Expr.expr -> Z3.Expr.expr
val mk_or : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_star : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

(* [on_star f g op xs] returns either [f xs] or [g op xs] depending on
   whether [op] is a star or not. Similarly for the other [on_*]
   functions. In other modules, you should prefer to use these instead of
   mentioning strings. *)
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
val on_string_const : (string -> 'a) -> 'a app_eval
val on_int_const : (int -> 'a) -> 'a app_eval
val on_op : Z3.FuncDecl.func_decl -> 'a app_eval_n

(* Example: let rec f e = cases (fun _->false) (recurse f) *)
val recurse : (Z3.Expr.expr -> Z3.Expr.expr) -> (Z3.Expr.expr -> Z3.Expr.expr)
val pp_expr : Z3.Expr.expr pretty_printer
