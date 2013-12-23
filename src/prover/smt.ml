open Corestar_std
open Debug

(** Z3 initialisation *)
(* we must open any log file before creating any context *)
let () =
  if (log log_smt) && (not (Z3.Log.open_ "smt.corestar.log")) then
    failwith "SMT logging is enabled but Z3 could not open smt.corestar.log.";;
let z3_ctx = Z3.mk_context !Config.z3_options

type sort = Expression.sort  (* p, p1, p2, q, ... *)
type symbol = string  (* s, s1, s2, *)
type term = Expression.t  (* t, t1, t2, *)
type var = Expression.var  (* x, y, ... *)

type check_sat_response = Sat | Unsat | Unknown

let uniq_id = ref 0
let str_map = StringHash.create 0
let sym_map = StringHash.create 0
(** remember the expressions that Z3 knows about *)
let expr_map = Expression.ExprHashMap.create 0

let bad_id_re = Str.regexp "[^a-zA-Z0-9]+"

let sanitize pre map id =
  try StringHash.find map id
  with Not_found -> begin
    let clean = Str.global_replace bad_id_re "" in
    let r = Printf.sprintf "%s-%s-%d" pre (clean id) (incr uniq_id; !uniq_id) in
    StringHash.add map id r; r
  end

let sanitize_sym = sanitize "sym" sym_map
let sanitize_str = sanitize "str" str_map
let sanitize_int = sanitize "int" str_map (* TODO: handle integers properly *)

let log_comment s = if log log_smt then Z3.Log.append ("; "^s^"\n")

(* TODO: ideally, this should be called before we exit *)
let close_log () = Z3.Log.close()

(* }}} *)

let z3_sort_of_sort = Z3.Sort.mk_uninterpreted_s z3_ctx

(* TODO: temporary hack to have homogeneous sorts. Should use [Expression.sort_of] *)
let ref_sort = z3_sort_of_sort "Ref"

let z3_solver = Z3.Solver.mk_simple_solver z3_ctx

let declare_fun sm ps st =
  Z3.FuncDecl.mk_func_decl_s z3_ctx (sanitize_sym sm) ps st

(* TODO: have proper typing; should use [Expression.sort_of]. *)
(** translate a coreStar expression [t] into a Z3 expression. Memoize the results in [expr_map]. *)
let rec z3_expr_of_expr =
  let rec repeat x = function [] -> [] | e :: ts -> x :: repeat x ts in
  let bool_sort = Z3.Boolean.mk_sort z3_ctx in
  let rec visit0 sort t =
    try Expression.ExprHashMap.find expr_map t
    with Not_found ->
      let e = Expression.match_ t
        (fun v -> (Z3.Expr.mk_const_s z3_ctx (sanitize_sym v) sort))
        (Expression.on_emp (c1 (Z3.Boolean.mk_true z3_ctx))
         & Expression.on_eq (visit2 ref_sort (Z3.Boolean.mk_eq z3_ctx))
         & Expression.on_fls (c1 (Z3.Boolean.mk_false z3_ctx))
         & Expression.on_neq (visit2bis ref_sort (Z3.Boolean.mk_distinct z3_ctx))
         & Expression.on_not (visit1 bool_sort (Z3.Boolean.mk_not z3_ctx))
         & Expression.on_or (visitn bool_sort (Z3.Boolean.mk_or z3_ctx))
         & Expression.on_star (visitn bool_sort (Z3.Boolean.mk_and z3_ctx))
         & Expression.on_string_const (fun s -> Z3.Expr.mk_const_s z3_ctx (sanitize_str s) sort)
         & Expression.on_int_const (fun n -> Z3.Expr.mk_const_s z3_ctx (sanitize_str n) sort)
         & (fun op ts ->
           let opdecl = declare_fun op (repeat ref_sort ts) sort in
           visitn ref_sort (Z3.Expr.mk_app z3_ctx opdecl) ts) ) in
      Expression.ExprHashMap.add expr_map t e;
      e
  and visit1 sort f1 t = f1 (visit0 sort t)
  and visit2 sort f2 =
    let f2bis = function
      | [e1; e2] -> f2 e1 e2
      | _ -> failwith "Internal error" in
    visit2bis sort f2bis
  and visit2bis sort f2 t1 t2 = visitn sort f2 [t1; t2]
  and visitn sort fn ts = fn (List.map (visit0 sort) ts) in
  visit0 bool_sort

let smt_listen () =
  match Z3.Solver.check z3_solver [] with
  | Z3.Solver.SATISFIABLE -> Sat
  | Z3.Solver.UNSATISFIABLE -> Unsat
  | Z3.Solver.UNKNOWN -> Unknown

let define_fun sm vs st tm  =
  let psorts = List.map snd vs in
  let params = List.map (fun (v,s) -> Z3.Expr.mk_const_s z3_ctx v (z3_sort_of_sort s)) vs in
  let fdecl = declare_fun sm (List.map z3_sort_of_sort psorts) (z3_sort_of_sort st) in
  let fx = Z3.Expr.mk_app z3_ctx fdecl params in
  let def = Z3.Boolean.mk_eq z3_ctx fx (z3_expr_of_expr tm) in
  let quantified_def =
    Z3.Quantifier.mk_forall_const z3_ctx params def
      None (* default weight (0) *)
      []   (* no patterns *)
      []   (* no nopatterns *)
      None (* quantifier_id *)
      None (* skolem_id *) in
  Z3.Solver.add z3_solver [Z3.Quantifier.expr_of_quantifier quantified_def]

let say e = Z3.Solver.add z3_solver [z3_expr_of_expr e]

let check_sat () =
  (* TODO: Handle (distinct ...) efficiently. *)
  let ss = StringHash.fold (fun _ -> ListH.cons) str_map [] in
  let ss = List.map (fun s -> Z3.Expr.mk_const_s z3_ctx s ref_sort) ss in
  if ss <> [] then
    Z3.Solver.add z3_solver [Z3.Boolean.mk_distinct z3_ctx ss];
  smt_listen ()

let push () =
  Z3.Solver.push z3_solver

let pop () =
  Z3.Solver.pop z3_solver 1
