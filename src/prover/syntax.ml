open Corestar_std
open Debug
open Format

type var = string

(** Z3 initialisation *)
let z3_ctx =
  (* we must open any log file before creating any context *)
  if log log_smt && not (Z3.Log.open_ "smt.corestar.log") then
    failwith "SMT logging is enabled but Z3 could not open smt.corestar.log.";
  if log log_smt then Z3.Log.append (Z3.Version.to_string);
  Z3.mk_context !Config.z3_options

let int_sort = Z3.Arithmetic.Integer.mk_sort z3_ctx
let string_sort = int_sort (* TODO: ugly hack? *)

let expr_compare = Z3.Expr.compare
let expr_equal = Z3.Expr.equal

(* {{{ strings stuff *)

let string_const_map = StringHash.create 0

let mk_string_const s =
  try StringHash.find string_const_map s
  with Not_found ->
    let e = Z3.Expr.mk_const_s z3_ctx s string_sort in
    StringHash.add string_const_map s e;
    e

let get_all_string_exprs () =
  StringHash.fold (fun _ -> ListH.cons) string_const_map []

(* }}} *)


let plvar_char = '%'
let pgvar_char = '@'
let lvar_char = '_'
let tpat_char = '?'
let vpat_char = '^'
let pure_char = '!'

let is_pgvar_name v = v.[0] = pgvar_char
let is_plvar_name v = v.[0] = plvar_char
let is_pvar_name v = v.[0] = plvar_char || v.[0] = pgvar_char
let is_lvar_name v = v.[0] = lvar_char
let is_tpat_name p = p.[0] = tpat_char
let is_vpat_name p = p.[0] = vpat_char

let var_name v = String.sub v 1 (String.length v - 1)

(* Workaround for Z3 interface.
  NOTE: Also be careful with [Z3.Expr.get_func_decl]. It's somewhat impossible
  to ensure it won't throw, so better to catch Z3Native.Exception everywhere
  [get_func_decl] is called. *)
let z3_is is e = (* HUGE HACK *)
  try is e with Z3native.Exception _ -> false
let z3_is_false = z3_is Z3.Boolean.is_false
let z3_is_or = z3_is Z3.Boolean.is_or
let z3_is_not = z3_is Z3.Boolean.is_not
let z3_is_eq = z3_is Z3.Boolean.is_eq
let z3_is_distinct = z3_is Z3.Boolean.is_distinct
let z3_is_const = z3_is Z3.Expr.is_const

(* watch out for code duplication below (is_var and is_const) *)
let is_pvar v = z3_is_const v && is_pvar_name (Z3.Expr.to_string v)
let is_plvar v = z3_is_const v && is_plvar_name (Z3.Expr.to_string v)
let is_pgvar v = z3_is_const v && is_pgvar_name (Z3.Expr.to_string v)
let is_lvar v = z3_is_const v && is_lvar_name (Z3.Expr.to_string v)
let is_tpat p = z3_is_const p && is_tpat_name (Z3.Expr.to_string p)
let is_vpat p = z3_is_const p && is_vpat_name (Z3.Expr.to_string p)

(* caution: code-duplication for optimisation purposes! *)
let is_var v =
  z3_is_const v &&
  (is_pvar_name (Z3.Expr.to_string v)
   || is_lvar_name (Z3.Expr.to_string v)
   || is_tpat_name (Z3.Expr.to_string v)
   || is_vpat_name (Z3.Expr.to_string v))
let is_const v = z3_is_const v && not
  (is_pvar_name (Z3.Expr.to_string v)
   || is_lvar_name (Z3.Expr.to_string v)
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

(* TODO: This is *not* a catch all case. it should have a continuation. *)
let on_app f e = f (Z3.Expr.get_func_decl e) (Z3.Expr.get_args e)

(* TODO: perhaps unfold more: variables, type of quant. *)
let on_quantifier f g e =
  if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr e)
  then f (Z3.Quantifier.get_body (Z3.Quantifier.quantifier_of_expr e))
  else g e

let on_op op_ref f g e =
  let b =
    try Z3.FuncDecl.equal op_ref (Z3.Expr.get_func_decl e)
    with Z3native.Exception _ -> false in
  if b then f (Z3.Expr.get_args e) else g e
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

let on_filter filt f g e =
  if filt e then f (Z3.Expr.get_args e) else g e
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
  if z3_is_const e && (Z3.Sort.equal (Z3.Expr.get_sort e) sort)
  then f (sort_transform e)
  else g e

let recurse f = on_app (fun op es -> Z3.FuncDecl.apply op (List.map f es))

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

(* TODO: why is mk_0 different from others? *)
let mk_0 op = Z3.Expr.mk_const_s z3_ctx op bool_sort
let mk_1 op e = Z3.FuncDecl.apply op [e]
let mk_2 op e f = Z3.FuncDecl.apply op [e; f]
let mk_n = Z3.FuncDecl.apply

let emp = Z3.FuncDecl.mk_func_decl_s z3_ctx "emp" [] bool_sort
let star = Z3.FuncDecl.mk_func_decl_s z3_ctx "*" [bool_sort; bool_sort] bool_sort

let mk_var s v = Z3.Expr.mk_const_s z3_ctx v s
let mk_plvar s v = mk_var s (String.make 1 plvar_char ^ v)
let mk_pgvar s v = mk_var s (String.make 1 pgvar_char ^ v)
let mk_lvar s v = mk_var s (String.make 1 lvar_char ^ v)
let mk_tpat s v = mk_var s (String.make 1 tpat_char ^ v)
let mk_vpat s v = mk_var s (String.make 1 vpat_char ^ v)
let mk_fresh_var s v = Z3.Expr.mk_fresh_const z3_ctx v s
let mk_fresh_lvar s v = mk_fresh_var s (String.make 1 lvar_char ^ v)
let mk_fresh_tpat s v = mk_fresh_var s (String.make 1 tpat_char ^ v)
let mk_fresh_vpat s v = mk_fresh_var s (String.make 1 vpat_char ^ v)

let mk_bool_plvar v = mk_plvar bool_sort v
let mk_bool_pgvar v = mk_pgvar bool_sort v
let mk_bool_lvar v = mk_lvar bool_sort v
let mk_bool_tpat v = mk_tpat bool_sort v
let mk_bool_vpat v = mk_vpat bool_sort v
let mk_fresh_bool_lvar v = mk_fresh_lvar bool_sort v
let mk_fresh_bool_tpat v = mk_fresh_tpat bool_sort v
let mk_fresh_bool_vpat v = mk_fresh_vpat bool_sort v

let mk_int_const x = Z3.Arithmetic.Integer.mk_const_s z3_ctx x
let mk_int_plvar v = mk_plvar int_sort v
let mk_int_pgvar v = mk_pgvar int_sort v
let mk_int_lvar v = mk_lvar int_sort v
let mk_int_tpat v = mk_tpat int_sort v
let mk_int_vpat v = mk_vpat int_sort v
let mk_fresh_int_lvar v = mk_fresh_lvar int_sort v
let mk_fresh_int_tpat v = mk_fresh_tpat int_sort v
let mk_fresh_int_vpat v = mk_fresh_vpat int_sort v

let mk_distinct = Z3.Boolean.mk_distinct z3_ctx
let mk_emp = Z3.FuncDecl.apply emp []
let mk_eq a b = Z3.Boolean.mk_eq z3_ctx a b
let mk_false = Z3.Boolean.mk_false z3_ctx
let mk_not a = Z3.Boolean.mk_not z3_ctx a
let mk_or a b = Z3.Boolean.mk_or z3_ctx [a; b]
let mk_star a b = mk_2 star a b

let mk_big_star es =
  let es = List.sort expr_compare es in
  match es with
  | [] -> mk_emp
  | [e] -> e (* these two cases to avoid introducing too many spurious stars *)
  | e::tl -> List.fold_left mk_star e tl


let on_emp f = on_0 emp f
let on_star f = on_2 star f
let on_false f = on_filter_0 z3_is_false f
let on_or f = on_filter z3_is_or f
let on_not f = on_filter_1 z3_is_not f
let on_eq f = on_filter_2 z3_is_eq f
let on_distinct f = on_filter z3_is_distinct f

let on_string_const f =
  on_const_of_sort string_sort Z3.Expr.to_string f

let on_int_const f =
  on_const_of_sort int_sort Z3.Arithmetic.Integer.get_int f

let is_pure_op e =
  try
    (Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e))).[0] = pure_char
  with Z3native.Exception _ -> false

(* this is shadowed by the memoised version below *)
let rec is_pure e =
  let c0 x () = x in
  let is_z3_bool_op e =
    Z3.Boolean.is_ite e
    || Z3.Boolean.is_and e
    || Z3.Boolean.is_or e
    || Z3.Boolean.is_iff e
    || Z3.Boolean.is_xor e
    || Z3.Boolean.is_not e
    || Z3.Boolean.is_implies e in
  let is_z3_pure_op e =
    Z3.Set.is_subset e
    || Z3.FiniteDomain.is_lt e
    || Z3.Relation.is_is_empty e
    || Z3.Arithmetic.is_le e
    || Z3.Arithmetic.is_ge e
    || Z3.Arithmetic.is_lt e
    || Z3.Arithmetic.is_gt e
    || Z3.BitVector.is_bv_ule e
    || Z3.BitVector.is_bv_sle e
    || Z3.BitVector.is_bv_uge e
    || Z3.BitVector.is_bv_sge e
    || Z3.BitVector.is_bv_ult e
    || Z3.BitVector.is_bv_slt e
    || Z3.BitVector.is_bv_ugt e
    || Z3.BitVector.is_bv_sgt e
    || Z3.BitVector.is_bv_comp e in
  let terr _ = failwith "INTERNAL: should be formula, not term (fuw3irj)" in
  ( on_string_const terr
  & on_int_const terr
  & on_var (c1 false) (* best effort *)
  & on_emp (c0 true)
  & on_false (c0 true)
  & on_star (fun a b -> is_pure a && is_pure b)
  & on_or (List.for_all is_pure)
  & on_not (fun e -> assert (is_pure e); true)
  & on_eq (c2 true)
  & on_distinct (c1 true)
  & on_quantifier is_pure
  & on_filter is_z3_bool_op (fun l -> assert(List.for_all is_pure l); true)
  & on_filter is_z3_pure_op (c1 true)
  & is_pure_op ) e

let mem_pure = ExprHashMap.create 0

(* TODO: do we want to gather statistics on cache hits? *)
let is_pure e =
  try ExprHashMap.find mem_pure e
  with Not_found ->
    let p = is_pure e in
    ExprHashMap.add mem_pure e p;
    p


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
