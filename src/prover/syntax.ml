open Corestar_std
open Debug
open Format

type var = string

(** Z3 initialisation *)
let z3_ctx =
  (* we must open any log file before creating any context *)
  if not (Z3.Log.open_ "smt.corestar.log") then
    failwith "SMT logging is enabled but Z3 could not open smt.corestar.log.";
  Z3.Log.append (Z3.Version.to_string);
  Z3.mk_context !Config.z3_options

(* This should really be in the Z3 bindings? *)
let expr_compare e1 e2 = Z3.AST.compare (Z3.Expr.ast_of_expr e1) (Z3.Expr.ast_of_expr e2)
let expr_equal e1 e2 = Z3.AST.equal (Z3.Expr.ast_of_expr e1) (Z3.Expr.ast_of_expr e2)

(* {{{ strings stuff *)

let string_const_map = StringHash.create 0
let string_sort = Z3.Sort.mk_uninterpreted_s z3_ctx "String"

let mk_string_const s =
  try StringHash.find string_const_map s
  with Not_found ->
    let e = Z3.Expr.mk_const_s z3_ctx s string_sort in
    StringHash.add string_const_map s e;
    e

let get_all_string_exprs () =
  StringHash.fold (fun _ -> ListH.cons) string_const_map []

(* }}} *)


(* TODO: these should be parameterisable *)
let pvar_re = Str.regexp "[@%$]" (* TODO: I'd prefer just [a-z]. *)
let lvar_re = Str.regexp "_"
let tpat_re = Str.regexp "\\?"
let vpat_re = Str.regexp "_" (* TODO: lval/vpat confusion? *)
let pure_re = Str.regexp "!"
let global_prefix = "$g"

let is_pvar_name v = Str.string_match pvar_re v 0
let is_lvar_name v = Str.string_match lvar_re v 0
let is_global_name v = StringH.starts_with global_prefix v
let is_tpat_name p = Str.string_match tpat_re p 0
let is_vpat_name p = Str.string_match vpat_re p 0

(* watch out for code duplication below (is_var and is_const) *)
let is_pvar v = Z3.Expr.is_const v && is_pvar_name (Z3.Expr.to_string v)
let is_lvar v = Z3.Expr.is_const v && is_lvar_name (Z3.Expr.to_string v)
let is_global v = Z3.Expr.is_const v && is_global_name (Z3.Expr.to_string v)
let is_tpat p = Z3.Expr.is_const p && is_tpat_name (Z3.Expr.to_string p)
let is_vpat p = Z3.Expr.is_const p && is_vpat_name (Z3.Expr.to_string p)

(* caution: code-duplication for optimisation purposes! *)
let is_var v = Z3.Expr.is_const v &&
  (is_pvar_name (Z3.Expr.to_string v)
   || is_lvar_name (Z3.Expr.to_string v)
   || is_global_name (Z3.Expr.to_string v)
   || is_tpat_name (Z3.Expr.to_string v)
   || is_vpat_name (Z3.Expr.to_string v))
let is_const v = Z3.Expr.is_const v && not
  (is_pvar_name (Z3.Expr.to_string v)
   || is_lvar_name (Z3.Expr.to_string v)
   || is_global_name (Z3.Expr.to_string v)
   || is_tpat_name (Z3.Expr.to_string v)
   || is_vpat_name (Z3.Expr.to_string v))

type 'a app_eval = (Z3.Expr.expr -> 'a) -> (Z3.Expr.expr -> 'a)
type 'a app_eval_0 = (unit -> 'a) -> 'a app_eval
type 'a app_eval_1 = (Z3.Expr.expr -> 'a) -> 'a app_eval
type 'a app_eval_2 = (Z3.Expr.expr -> Z3.Expr.expr -> 'a) -> 'a app_eval
type 'a app_eval_n = (Z3.Expr.expr list -> 'a) -> 'a app_eval

(* NOTE: The main point of [on_*] functions is to avoid using strings in other
places in the codebase, because that is bug-prone. *)
let on_const fconst fapp e = if is_const e then fconst e else fapp e
let on_var f g e = if is_var e then f e else g e
let on_app f e = f (Z3.Expr.get_func_decl e) (Z3.Expr.get_args e)

let on_op op_ref f g e =
  let op = Z3.Expr.get_func_decl e in
  if Z3.FuncDecl.equal op op_ref then f (Z3.Expr.get_args e)
  else g e
let on_0 op_ref f =
  let f = function
    | [] -> f ()
    | _ -> failwith ("INTERNAL: "^ (Z3.FuncDecl.to_string op_ref) ^ " should have arity 0" ) in
  on_op op_ref f
let on_1 op_ref f =
  let f = function
    | [e] -> f e
    | _ -> failwith ("INTERNAL: "^ (Z3.FuncDecl.to_string op_ref) ^ " should have arity 1" ) in
  on_op op_ref f
let on_2 op_ref f =
  let f = function
    | [e1; e2] -> f e1 e2
    | _ -> failwith ("INTERNAL: "^ (Z3.FuncDecl.to_string op_ref) ^ " should have arity 2" ) in
  on_op op_ref f

let on_filter filt f g e = if filt e then f (Z3.Expr.get_args e) else g e
let on_filter_0 filt f g e =
  let f = function
    | [] -> f ()
    | _ -> failwith ("INTERNAL: "^ (Z3.Expr.to_string e) ^ " should have arity 0" ) in
  on_filter filt f g e
let on_filter_1 filt f g e =
  let f = function
    | [e1] -> f e1
    | _ -> failwith ("INTERNAL: "^ (Z3.Expr.to_string e) ^ " should have arity 1" ) in
  on_filter filt f g e
let on_filter_2 filt f g e =
  let f = function
    | [e1; e2] -> f e1 e2
    | _ -> failwith ("INTERNAL: "^ (Z3.Expr.to_string e) ^ " should have arity 2" ) in
  on_filter filt f g e

let on_const_of_sort sort sort_transform f g e =
  if Z3.Expr.is_const e && Z3.Sort.equal (Z3.Expr.get_sort e) sort
  then f (sort_transform e)
  else g e

let recurse f op es = Z3.FuncDecl.apply op (List.map f es)

(** int_of_bool *)
let iob b = if b then 1 else 0

let stem v =
  let i = iob (v.[0] = '_') in
  let len = (try String.index v '!' with Not_found -> String.length v) - i in
  String.sub v i len

(* Assumes the input is one of 'STEM', '_STEM', or '_STEM!ID'.
Produces '_STEM!ID' where ID is fresh for the given STEM. *)
let freshen v =
  let old_stem = stem (Z3.Expr.to_string v) in
  let new_name = Printf.sprintf "_%s" old_stem in
  Z3.Expr.mk_fresh_const z3_ctx new_name (Z3.Expr.get_sort v)

(* TODO: Memoize if profiling shows that this is slow. *)
let rec size e =
  (on_const (c1 1)
   & on_var (c1 1)
   & on_app (fun _ xs -> List.fold_left (+) 1 (List.map size xs))) e

module HashableExpr = struct
  type t = Z3.Expr.expr
  let hash = Z3.AST.hash @@ Z3.Expr.ast_of_expr
  let equal = expr_equal
  let compare = expr_compare
end

module ExprSet = Set.Make(HashableExpr)
module ExprMap = Map.Make(HashableExpr)
module ExprHashSet = HashSet.Make(HashableExpr)
module ExprHashMap = Hashtbl.Make(HashableExpr)

let vars x =
  let vs = ExprHashSet.create 0 in
  let rec f expr =
    (on_var (fun _ -> ExprHashSet.add vs expr)
     & on_app (fun _ xs -> List.iter f xs ))
      expr in
  let g expr a = expr::a in
  f x; ExprHashSet.fold g vs []

let bool_sort = Z3.Boolean.mk_sort z3_ctx

let mk_0 op = Z3.Expr.mk_const_s z3_ctx op bool_sort
let mk_1 op a = Z3.FuncDecl.apply op [a]
let mk_2 op a b = Z3.FuncDecl.apply op [a; b]

let emp = Z3.FuncDecl.mk_func_decl_s z3_ctx "emp" [] bool_sort
let star = Z3.FuncDecl.mk_func_decl_s z3_ctx "*" [bool_sort; bool_sort] bool_sort

let int_sort = Z3.Arithmetic.Integer.mk_sort z3_ctx
let mk_var v = Z3.Expr.mk_const_s z3_ctx v int_sort
let mk_pvar v = assert (is_pvar_name v); mk_var v
let mk_gvar v = assert (is_global_name v); mk_var v
let mk_lvar v = assert (is_lvar_name v); mk_var v

let mk_emp = Z3.FuncDecl.apply emp []
let mk_eq a b = Z3.Boolean.mk_eq z3_ctx a b
let mk_or a b = Z3.Boolean.mk_or z3_ctx [a; b]
let mk_not a = Z3.Boolean.mk_not z3_ctx a
let mk_star a b = mk_2 star a b

(* TODO: Move mk_big_star and on_big_star to Prover. *)
let mk_big_star es =
  let es = List.sort expr_compare es in
  match es with
  | [] -> mk_emp
  | [e] -> e (* these two cases to avoid introducing too many spurious stars *)
  | e::tl -> List.fold_left mk_star e tl

let on_emp f = on_0 emp f
let on_star f = on_2 star f
(** if [e] is of the form "e1 * (e2 * (... * en))" where en is not
    itself of the form "en' * en''", call [f] on the list [e1; e2; ...;
    en] else call [g e]*)
let on_big_star f g e =
  let rec descend_in_stars l =
    on_star (fun e1 e2 -> descend_in_stars (e1::l) e2)
    & (fun e -> if l = [] then g e else f (List.rev (e::l))) in
  descend_in_stars [] e

let on_false f = on_filter_0 Z3.Expr.is_false f
let on_or f = on_filter Z3.Expr.is_or f
let on_not f = on_filter_1 Z3.Expr.is_not f
let on_eq f = on_filter_2 Z3.Expr.is_eq f
let on_distinct f = on_filter Z3.Expr.is_distinct f

let on_string_const f = on_const_of_sort string_sort Z3.Expr.to_string f

let on_int_const f =
  on_const_of_sort (Z3.Arithmetic.Integer.mk_sort z3_ctx) Z3.Arithmetic.Integer.get_int f

let is_pure_op e =
  Str.string_match
    pure_re
    (Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)))
    0

let rec is_pure e =
  let c0 x () = x in
  let terr _ = failwith "INTERNAL: should be formula, not term" in
  ( on_string_const terr
  & on_int_const terr
  & on_var terr
  & on_emp (c0 true)
  & on_false (c0 true)
  & on_big_star (List.for_all is_pure)
  & on_or (List.for_all is_pure)
  & on_not (fun e -> assert (is_pure e); true)
  & on_eq (c2 true)
  & on_distinct (c1 true)
  & is_pure_op ) e

(* NOTE: pretty printing is for debug, so don't rely on it for anything else *)

(* close to SMT-LIB's language *)
let rec pp_expr_prefix f = pp_string f @@ Z3.Expr.to_string

(* WARNING: close to input language, but somewhat mangled wrt data structure *)
let rec pp_expr_infix f e =
  let pp_n op = fprintf f "@[(%a)@]" (pp_list_sep op pp_expr_infix) in
  let pp_2 op e1 e2 = pp_n op [e1; e2] in
  let pp_1 op e = fprintf f "@[%s%a@]" op pp_expr_infix e in
  let pp_0 op () = fprintf f "%s" op in
  (on_string_const (fprintf f "\"%s\"")
   & on_int_const (pp_int f)
   & on_var (fun e -> fprintf f "%s" (Z3.Expr.to_string e))
   & on_emp (pp_0 "emp")
   & on_false (pp_0 "false")
   & on_star (pp_2 " * ")
   & on_or (pp_n " || ")
   & on_not (pp_1 "!")
   & on_eq (pp_2 "=")
   & on_distinct (pp_n "!=")
   & on_app (fun op es -> fprintf f "@[%s(%a)@]" (Z3.Symbol.to_string (Z3.FuncDecl.get_name op)) (pp_list_sep ", " pp_expr_infix) es))
    e

(* NOTE: This function should be used *only* for debug. The [pp_prefix] version
is a verbatim dump of the data structure, and should be preferred. The
[pp_expr_infix] version is a hack that you might want to use if you want to print
expressions, edit them, then read them back with corestar's parser. All this
while debugging, of course.*)
let pp_expr = pp_expr_prefix
