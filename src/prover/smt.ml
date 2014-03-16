open Corestar_std
open Debug
open Format

type check_sat_response = Sat | Unsat | Unknown

let log_comment s = if log log_smt then Z3.Log.append ("; "^s^"\n")

let z3_ctx = Syntax.z3_ctx

let z3_solver = Z3.Solver.mk_simple_solver z3_ctx

let smt_listen () =
(*   printf "EXECUTING Z3@\n@?"; *)
  let r = Z3.Solver.check z3_solver [] in
(*   printf "REVIVING Z3@\n@?"; *)
  match r with
  | Z3.Solver.SATISFIABLE -> Sat
  | Z3.Solver.UNSATISFIABLE -> Unsat
  | Z3.Solver.UNKNOWN -> Unknown

(** replace function symbol [f] with [g] in [e] *)
let rewrite f g e =
  let cache = Syntax.ExprHashMap.create 127 in (* Jules: I picked 127 at random... *)
  let rec rewrite_app op args =
    let new_op = if Z3.FuncDecl.equal op f then g else op in
    let new_args = List.map rewrite_expr args in
(*    Format.fprintf logf "Translated args = %a to %a@." (pp_list_sep "," Syntax.pp_expr) args (pp_list_sep "," Syntax.pp_expr) new_args; *)
    Z3.FuncDecl.apply new_op new_args
  and rewrite_expr e =
    try Syntax.ExprHashMap.find cache e
    with Not_found ->
      let new_e = Syntax.on_app rewrite_app e in
      Syntax.ExprHashMap.add cache e new_e;
      new_e in
  rewrite_expr e

(* hack to get the function symbol associated with "and" in
   Z3. Probably simplifiable by declaring a symbol called "and" of the
   right type, which Z3 should hopefully recognise as boolean
   conjunction (afaict Z3 doesn't distinguish between symbols with the
   same name & type!). We could also write [rewrite] above differently
   so as to be able to use Boolean.mk_and in [rewrite_star_to_and]. *)
let and_func_decl =
  let a = Z3.Expr.mk_const_s z3_ctx "a" (Z3.Boolean.mk_sort z3_ctx) in
  let b = Z3.Expr.mk_const_s z3_ctx "b" (Z3.Boolean.mk_sort z3_ctx) in
  let e = Z3.Boolean.mk_and z3_ctx [a; b] in
  Z3.Expr.get_func_decl e

(** rewrite_star_to_and [e] replaces occurences of "*" in [e] with the boolean conjunction "and" *)
let rewrite_star_to_and = rewrite Syntax.star and_func_decl

(** say [e] tells Z3 to assert [e] (assert is a keyword) *)
(* TODO: Assert that e is pure? But perhaps sometimes we *want* to send stars to Z3. *)
let say e =
  (* Format.fprintf logf "SMT: previous kernel: %s@." (Z3.Solver.to_string z3_solver); *)
  (* Format.fprintf logf "SMT: saying %a, translated to %a@." Syntax.pp_expr e Syntax.pp_expr (rewrite_star_to_and e); *)
  Z3.Solver.add z3_solver [rewrite_star_to_and e];
  (* Format.fprintf logf "SMT: new kernel: %s@." (Z3.Solver.to_string z3_solver); *)
  ()

(* Jules: TOFIX: we don't use this and it's complicated... oh well, it might be useful at some point or for front-ends. *)
let define_fun sm vs st tm  =
  let psorts = List.map snd vs in
  let params = List.map (fun (v,s) -> Z3.Expr.mk_const_s z3_ctx v s) vs in
  let fdecl = Z3.FuncDecl.mk_func_decl_s z3_ctx sm psorts st in
  let fx = Z3.Expr.mk_app z3_ctx fdecl params in
  let def = Z3.Boolean.mk_eq z3_ctx fx tm in
  let quantified_def =
    Z3.Quantifier.mk_forall_const z3_ctx params def
      None (* default weight (0) *)
      []   (* no patterns *)
      []   (* no nopatterns *)
      None (* quantifier_id *)
      None (* skolem_id *) in
  say (Z3.Quantifier.expr_of_quantifier quantified_def)

let check_sat () =
  (* TODO: Handle (distinct ...) efficiently. In particular, only add
     distinct for strings that actually appear in the current goal and
     assumptions. *)
  let ss = Syntax.get_all_string_exprs () in
  (* Z3 segfaults if we use mk_distinct with < 2 elements *)
  if List.length ss > 1 then
    say (Z3.Boolean.mk_distinct z3_ctx ss);
  smt_listen ()

let push () = Z3.Solver.push z3_solver
let pop () = Z3.Solver.pop z3_solver 1
