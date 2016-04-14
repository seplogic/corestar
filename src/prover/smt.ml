open Corestar_std
open Debug
open Format

type check_sat_response = Sat | Unsat | Unknown

let z3_ctx = Syntax.z3_ctx

let z3_solver = Z3.Solver.mk_simple_solver z3_ctx

(* (= emp true) *)
let emp_is_true =
  Syntax.mk_eq Syntax.mk_emp (Z3.Boolean.mk_true z3_ctx)

let impure_stack = ref [false]
let impure_count = ref 0
  (* !(List.hd impure_stack) says if there was an impure assertion since the
  last push; !impure_count is the number of true elements in !impure_stack. *)
let set_impure b = match !impure_stack with
  | c :: cs ->
      if b && not c then incr impure_count;
      impure_stack := (b || c) :: cs
  | [] -> failwith "!impure_stack shouldn't be empty (9wq8edj)"
let push_impure_stack () =
  impure_stack := false :: !impure_stack
let pop_impure_stack () = match !impure_stack with
  | c :: cs ->
      if c then decr impure_count;
      impure_stack := cs
  | [] -> failwith "!impure_stack shouldn't be empty (id8nwb)"
let is_impure () = !impure_count > 0

(** rewrite_star_to_and [e] replaces occurences of "*" in [e] with the boolean conjunction "and" *)
let rewrite_star_to_and e =
  let cache = Syntax.ExprHashMap.create 0 in
  let rec rewrite_star l = Z3.Boolean.mk_and z3_ctx (List.map rewrite_expr l)
  and rewrite_expr e =
    try Syntax.ExprHashMap.find cache e
    with Not_found ->
      let mk_quantifier body universal bounds weight pats =
        Z3.Expr.update e [rewrite_expr body] in
      let new_e =
        (Syntax.on_var id
         & Syntax.on_quantifier mk_quantifier
         & Syntax.on_star rewrite_star
         & Syntax.recurse rewrite_expr) e in
      Syntax.ExprHashMap.add cache e new_e;
      new_e in
  rewrite_expr e

(** say [e] tells Z3 to assert [e] (assert is a keyword) *)
let say e =
  (* if (not (Syntax.is_pure e)) then *)
  (*   Format.fprintf Debug.logf "@{Impure: %a@}@\n" Syntax.pp_expr e; *)
  let pure = Syntax.is_pure e in
  set_impure (not pure);
  Z3.Solver.add z3_solver [if pure then rewrite_star_to_and e else e]

let declare_fun _ _ _ =
  failwith "TODO"

let dump_solver () = print_endline (Z3.Solver.to_string z3_solver)

let memoise = Syntax.ExprHashMap.create 0
let smt_hit, smt_miss = ref 0, ref 0

let check_sat () =
  (* TODO: Handle (distinct ...) efficiently. In particular, only add
     distinct for strings that actually appear in the current goal and
     assumptions. *)
  let ss = Syntax.get_all_string_exprs () in
  let es =
    (* Z3 segfaults if we use mk_distinct with < 2 elements *)
    (if List.length ss >= 2 then [Z3.Boolean.mk_distinct z3_ctx ss] else [])
    @(if is_impure () then [] else [emp_is_true]) in
  Z3.Solver.push z3_solver;
  Z3.Solver.add z3_solver es;
  let ass = Z3.Boolean.mk_and z3_ctx (Z3.Solver.get_assertions z3_solver) in
  let r =
    try
      let r = Syntax.ExprHashMap.find memoise ass in
      incr smt_hit;
      r
    with Not_found -> (
      incr smt_miss;
      let r = (match Z3.Solver.check z3_solver [] with
	| Z3.Solver.SATISFIABLE -> Sat
	| Z3.Solver.UNSATISFIABLE -> Unsat
	| Z3.Solver.UNKNOWN -> Unknown) in
      Syntax.ExprHashMap.add memoise ass r;
      r) in
  Z3.Solver.pop z3_solver 1;
  r

let push () = push_impure_stack (); Z3.Solver.push z3_solver
let pop () = pop_impure_stack (); Z3.Solver.pop z3_solver 1

let print_stats () =
  if log log_stats then begin
    fprintf logf "smt_hit %d smt_miss %d@\n" !smt_hit !smt_miss;
    let smt_stats = Z3.Solver.get_statistics z3_solver in
    let smt_stats = Z3.Statistics.to_string smt_stats in
    fprintf logf "SMT stats: %s@\n" smt_stats
  end
