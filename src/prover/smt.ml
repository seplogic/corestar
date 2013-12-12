(* TODO: This should be ported to Z3's OCAML API. *)

open Corestar_std
open Debug
open Printf
open Scanf
open Z3

(** Z3 initialisation *)
(* we must open any log file before creating any context *)
let () =
  if (log log_smt) && (not (Log.open_ "smt.corestar.log")) then
    failwith "SMT logging is enabled but Z3 could not open smt.corestar.log.";;
let z3_ctx = Z3.mk_context !Config.z3_options

type sort = Expression.sort  (* p, p1, p2, q, ... *)
type symbol = string  (* s, s1, s2, *)
type term = Expression.t  (* t, t1, t2, *)
type var = Expression.var  (* x, y, ... *)

type check_sat_response = Sat | Unsat | Unknown

(* TODO: The lhs is brittle: It must be whatever [Expression] uses internally. *)
let interpreted =
  [ "!=", "distinct"
  ; "*", "and"
  ; "==", "="
  ; "emp", "true"
  ; "fls", "false"
  ; "not", "not"
  ; "or", "or" ]

(* TODO: The name [identities] is bad. *)
let identities =
  [ "and", "true"
  ; "or", "false" ]

let uniq_id = ref 0
let str_map = StringHash.create 0
let sym_map = StringHash.create 0
let () = List.iter (uncurry (StringHash.add sym_map)) interpreted
(** remember the expressions that Z3 knows about *)
let expr_map = Expression.ExprHashMap.create 0

let bad_id_re = Str.regexp "[^a-zA-Z0-9]+"

let sanitize pre map id =
  try StringHash.find map id
  with Not_found -> begin
    let clean = Str.global_replace bad_id_re "" in
    let r = sprintf "%s-%s-%d" pre (clean id) (incr uniq_id; !uniq_id) in
    StringHash.add map id r; r
  end

let sanitize_sym = sanitize "sym" sym_map
let sanitize_str = sanitize "str" str_map
let sanitize_int = sanitize "int" str_map (* TODO: handle integers properly *)

let log_comment s = if log log_smt then Log.append ("; "^s^"\n")

(* TODO: ideally, this should be called before we exit *)
let close_log () = Log.close()

let declared = ref [StringHash.create 0]

let declared_sort s =
  let rec loop = function
    | [] -> raise Not_found
    | h :: hs -> (try StringHash.find h s with Not_found -> loop hs) in
  loop !declared

let declared_push () =
  declared := StringHash.create 0 :: !declared

let declared_pop () =
  declared := List.tl !declared;
  assert (!declared <> [])

let is_predeclared =
  let s = List.map snd interpreted in
  let s = List.fold_right StringSet.add s StringSet.empty in
  flip StringSet.mem s

let is_declared s =
  is_predeclared s
  || (try ignore (declared_sort s); true with Not_found -> false)

let find_op op =
 try List.assoc op identities
 with Not_found -> op

(* }}} *)

let z3_sort_of_sort = Sort.mk_uninterpreted_s z3_ctx

(* TODO: temporary hack to have homogeneous sorts. Should use [Expression.sort_of] *)
let ref_sort = z3_sort_of_sort "Ref"

let z3_solver = Solver.mk_simple_solver z3_ctx

let declare_fun sm ps st =
  FuncDecl.mk_func_decl_s z3_ctx (sanitize_sym sm) ps st

(* TODO: have proper typing; should use [Expression.sort_of]. *)
(** translate a coreStar expression [t] into a Z3 expression. Memoize the results in [expr_map]. *)
let rec z3_expr_of_expr =
  let rec repeat x = function [] -> [] | e :: ts -> x :: repeat x ts in
  let bool_sort = Boolean.mk_sort z3_ctx in
  let rec visit0 sort t =
    try Expression.ExprHashMap.find expr_map t
    with Not_found ->
      let e = Expression.match_ t
	(fun v -> (Expr.mk_const_s z3_ctx (sanitize_sym v) sort))
	(Expression.on_emp (c1 (Boolean.mk_true z3_ctx))
	 & Expression.on_eq (visit2 ref_sort (Boolean.mk_eq z3_ctx))
	 & Expression.on_fls (c1 (Boolean.mk_false z3_ctx))
	 & Expression.on_neq (visit2bis ref_sort (Boolean.mk_distinct z3_ctx))
	 & Expression.on_not (visit1 bool_sort (Boolean.mk_not z3_ctx))
	 & Expression.on_or (visitn bool_sort (Boolean.mk_or z3_ctx))
	 & Expression.on_star (visitn bool_sort (Boolean.mk_and z3_ctx))
	 & Expression.on_string_const (fun s -> Expr.mk_const_s z3_ctx (sanitize_str s) sort)
	 & Expression.on_int_const (fun n -> Expr.mk_const_s z3_ctx (sanitize_str n) sort)
	 & (fun op ts ->
	   let opdecl = declare_fun op (repeat ref_sort ts) sort in
	   visitn ref_sort (Expr.mk_app z3_ctx opdecl) ts) ) in
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
  match Solver.check z3_solver [] with
  | Solver.SATISFIABLE -> Sat
  | Solver.UNSATISFIABLE -> Unsat
  | Solver.UNKNOWN -> Unknown

let define_fun sm vs st tm  =
  let psorts = List.map snd vs in
  let params = List.map (fun (v,s) -> Expr.mk_const_s z3_ctx v (z3_sort_of_sort s)) vs in
  let fdecl = declare_fun sm (List.map z3_sort_of_sort psorts) (z3_sort_of_sort st) in
  let fx = Expr.mk_app z3_ctx fdecl params in
  let def = Boolean.mk_eq z3_ctx fx (z3_expr_of_expr tm) in
  let quantified_def =
    Quantifier.mk_forall_const z3_ctx params def
      None (* default weight (0) *)
      []   (* no patterns *)
      []   (* no nopatterns *)
      None (* quantifier_id *)
      None (* skolem_id *) in
  Solver.add z3_solver [Quantifier.expr_of_quantifier quantified_def]

let say e = Solver.add z3_solver [z3_expr_of_expr e]

let check_sat () =
  (* TODO: Handle (distinct ...) efficiently. *)
  let ss = StringHash.fold (fun _ -> ListH.cons) str_map [] in
  let ss = List.map (fun s -> Expr.mk_const_s z3_ctx s ref_sort) ss in
  if ss <> [] then
    Solver.add z3_solver [Boolean.mk_distinct z3_ctx ss];
  smt_listen ()

let push () =
  declared_push ();
  Solver.push z3_solver

let pop () =
  declared_pop ();
  Solver.pop z3_solver 1
