(* Modules *) (* {{{ *)
open Corestar_std
open Debug
open Format
open Smt

module Expr = Expression

(* }}} *)
type frame_and_antiframe =
  { frame : Expr.t
  ; antiframe : Expr.t }

(* Helper functions for prover rules. *) (* {{{ *)
let smt_is_valid a =
  Smt.push ();
  Smt.say (Expr.mk_not a);
  let r = match Smt.check_sat () with Smt.Unsat -> true | _ -> false in
  Smt.pop ();
  r

let smt_implies a b =
  let ok_n = [ Expr.on_star; Expr.on_or ] in
  let ok_2 = [ Expr.on_eq; Expr.on_neq ] in
  let ok_1 = [ Expr.on_not ] in
  let stop_op = [ Expr.on_string_const; Expr.on_int_const ] in
  let rec is_ok e =
    let f _ _ = false in
    let f = List.fold_right ((|>) are_all_ok) ok_n f in
    let f = List.fold_right ((|>) are_both_ok) ok_2 f in
    let f = List.fold_right ((|>) is_ok) ok_1 f in
    let f = List.fold_right ((|>) (fun _ -> true)) stop_op f in
    Expr.cases (fun _ -> true) f e
  and are_all_ok es = List.for_all is_ok es
  and are_both_ok a b = is_ok a && is_ok b in
  are_both_ok a b && smt_is_valid (Expr.mk_or (Expr.mk_not a) b)

(* }}} *)
(* Prover rules, including those provided by the user. *) (* {{{ *)
type named_rule =
  { rule_name : string (* For debug *)
  ; rule_apply : Calculus.sequent -> Calculus.sequent list list }
  (* If (rule_apply x) is [[a;b];[c]], then a and b together are sufficient
  to prove x, and so is c alone. *)

let id_rule =
  { rule_name = "identity axiom"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; _ } ->
      if Expr.equal hypothesis conclusion then [[]] else []) }

let smt_pure_rule =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; _ } ->
      if smt_implies hypothesis conclusion then [[]] else []) }

(* A root-leaf path of an expression must match ("or"?; "star"?; "not"?; OTHER).
The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
and "not". *)
(* NOTE: very inefficient; fix if profiler complains *)
let normalize =
  let concatMap f xs = List.concat (List.map f xs) in
  let module X = struct
    type t = { on: 'a. 'a Expr.app_eval_n; mk: Expr.t list -> Expr.t }
  end in
  let rec assoc this =
    (* TODO: add sorting *)
    let r op es = Expr.mk_app op (List.map (assoc this) es) in
    let u x = [x] in
    let ur op es = u (r op es) in
    let rec split es =
      Expr.cases (u @@ Expr.mk_var) (this.X.on (concatMap split) ur) es in
    let remk_this es = this.X.mk (concatMap split es) in
    Expr.cases Expr.mk_var (this.X.on remk_this r) in
(*  let not_not _ = failwith "TODO" in
  let star_below_or _ = failwith "TODO" in
  let forbid _ = failwith "TODO" in
  let del_id _ = failwith "TODO" in
  let kill_unit _ = failwith "TODO" in *)
  let rec fix f e1 =
    let e2 = f e1 in
    if Expr.equal e1 e2 then e1 else fix f e2 in
  let fs =
    [ assoc { X.on = Expr.on_star; mk = Expr.mk_big_star }
    ; assoc { X.on = Expr.on_or; mk = Expr.mk_big_or }
(*    ; not_not
    ; star_below_or
    ; forbid Expr.on_not Expr.on_or
    ; forbid Expr.on_not Expr.on_star
    ; del_id Expr.on_star Expr.emp
    ; del_id Expr.on_or Expr.fls
    ; kill_unit Expr.on_or
    ; kill_unit Expr.on_star *) ] in
  let f = List.fold_left (@@) id fs in
  fix f

(* find_matches and helpers *) (* {{{ *)
let unique_extractions l =
  let rec inner acc = function
    | [] -> []
    | x::xs ->
      let rest = (List.map (fun (y, ys) -> (y, x::ys)) (inner (x::acc) xs)) in
      if List.mem x acc then rest
      else (x, xs)::rest in
  inner [] l

(* splits a list of equal elements *)
let rec splits = function
  | [] -> [([], [])]
  | x::xs ->
    ([], x::xs)::(List.map (fun (yes, no) -> (x::yes, no)) (splits xs))

(*
  assumes elements of [l] to be sorted
  (actually just that equal elements are next to each other)
*)
let rec unique_subsets l =
  let rec inner acc = function
    | [] -> splits acc
    | x::xs ->
      if List.mem x acc then inner (x::acc) xs
      else
	inner [x] xs >>= (fun (yes, no) -> splits acc |> List.map (fun (to_yes, to_no) -> (to_yes@yes, to_no@no))) in
  inner [] l


type bindings = Expr.t StringMap.t

let try_find x m = try Some (StringMap.find x m) with Not_found -> None

let cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) =
  let on_pvar pv = Expr.cases (on_pvar_var pv) (on_pvar_op pv) e in
  let on_pop po ps = Expr.cases (on_pop_var po ps) (on_pop_op po ps) e in
  Expr.cases on_pvar on_pop p

(* Not needed as eq and neq are not comassoc
   They are not, as normalize would not do the right thing on them
let on_pair f a b = f [a; b]
*)

let on_comassoc handle_comassoc handle_skew o es =
  Expr.on_star (handle_comassoc o)
 (Expr.on_or (handle_comassoc o) handle_skew) o es
(*
 (Expr.on_eq (on_pair handle_comassoc)
 (Expr.on_neq (on_pair handle_comassoc)
  handle_skew))))
*)

(*
  This normalization is needed in the matcher
  because the matcher implicitly applies it to the pattern
  it has to be done also to the expression in order to obtain a match
*)
let normalize_comassoc e =
  let unfold o = function [x] -> x | _ -> e in
  Expr.cases (fun _ -> e) (on_comassoc unfold (fun _ _ -> e)) e

type match_result =
  | Done of bindings
  | More of bindings * (Expr.t * Expr.t)

(*
  Expr.t -> Expr.t -> bindings list
  Assumes that e does not contain pattern variables

  input bs is one assignment, the current branch we are exploring
  output is list of assignments, all possible extensions which leads to a match
*)
let rec find_matches bs (p, e) =
  let bind pv =
    begin
      match try_find pv bs with
	| None -> [Done (StringMap.add pv e bs)]
	| Some oe -> if e = oe then [Done bs] else []
    end in
  let on_pvar_var pv _ = bind pv in
  let on_pvar_op pv _ _ = if Expr.is_tpat pv then bind pv else [] in
  let on_pop_var _ _ _ = [] in
  let on_pop_op po ps o es =
    if po <> o then []
    else
      let handle_comassoc _ _ =
	begin
	  let mk_o l = Expr.mk_app o l in
	  match ps with
	    | [] -> [Done bs]
	    | [x] -> List.map (fun m -> Done m) (find_matches bs (x, normalize_comassoc e))
	    | ext_p::rest_p ->
	      begin
		let unspecific v =
		  let is_more (yes, no) =
		    let to_bind = normalize_comassoc (mk_o yes) in
		    match try_find v bs with
		      | None -> Some (More (StringMap.add v to_bind bs, (mk_o rest_p, mk_o no)))
		      | Some oyes ->
			if oyes = to_bind then Some (More (bs, (mk_o rest_p, mk_o no)))
			else None in
		  unique_subsets es |> map_option is_more in
		let specific () =
		  match es with
		    | [] -> [Done bs]
		    | [x] -> List.map (fun m -> Done m) (find_matches bs (ext_p, x))
		    | _ ->
		      let ext_match (ext_e, rest_e) =
			let mk_more m = More (m, (mk_o rest_p, mk_o rest_e)) in
			List.map mk_more (find_matches bs (ext_p, ext_e)) in
		      unique_extractions es >>= ext_match in
		Expr.cases
		  (fun v -> if Expr.is_tpat v then unspecific v else specific ())
		  (fun _ _ -> specific ())
		  ext_p
	      end
	end in
      let handle_skew _ _ =
	if List.length ps <> List.length es then []
	else
	  let todos = List.combine ps es in
	  let process_todo acc (tp, te) =
	    acc >>= (flip find_matches (tp, te)) in
	  let result = List.fold_left process_todo [bs] todos in
	  List.map (fun r -> Done r) result in
      on_comassoc handle_comassoc handle_skew po ps in
  let matches = cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) in
  let process_match = function
    | Done final_bs -> [final_bs]
    | More (next_bs, next_pair) ->
      (*      Format.printf "<processing more %d>" (List.length next_bs); *)
      find_matches next_bs next_pair in
  matches >>= process_match

let find_sequent_matches bs ps s =
  let fm pat exp bs = find_matches bs (pat, exp) in
  fm ps.Calculus.frame s.Calculus.frame bs >>=
    fm ps.Calculus.hypothesis s.Calculus.hypothesis >>=
    fm ps.Calculus.conclusion s.Calculus.conclusion
(* }}} *)

let rec instantiate bs p =
  let on_var pv = match try_find pv bs with None -> Expr.mk_var pv | Some e -> e in
  let on_op po ps = Expr.mk_app po (List.map (instantiate bs) ps) in
  Expr.cases on_var on_op p

let instantiate_sequent bs s =
  { Calculus.frame = instantiate bs s.Calculus.frame
  ; hypothesis = instantiate bs s.Calculus.hypothesis
  ; conclusion = instantiate bs s.Calculus.conclusion }

let rules_of_calculus c =
  let apply_rule_schema rs s = (* RLP: Should we refer to some bindings here? *)
    let m = find_sequent_matches StringMap.empty rs.Calculus.goal_pattern s in
    List.map (fun bs -> List.map (instantiate_sequent bs) rs.Calculus.subgoal_pattern) m in
  let to_rule rs =
    { rule_name = rs.Calculus.schema_name
    ; rule_apply = apply_rule_schema rs } in
  id_rule :: smt_pure_rule :: List.map to_rule c

(* }}} *)
(* The main proof-search algorithm. *) (* {{{ *)

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with
with score [> Backtrack.max_penalty] needs a proof.  Anything in-between is kind
of acceptable as a leaf, but we should keep looking for something better.
  TODO: we may want min_penalty and max_penalty decrease with the level n
  TODO: we may want to count only once a leaf appearing twice
  TODO: we may want to partly cache the results of proving
*)
let rec solve rules penalty n { Calculus.frame; hypothesis; conclusion } =
  if log log_prove then fprintf logf "@[<2>";
  let goal =
    { Calculus.frame = normalize frame
    ; hypothesis = normalize hypothesis
    ; conclusion = normalize conclusion } in
  let leaf = ([goal], penalty goal) in
  let result =
    if n = 0 then leaf else begin
      let process_rule r =
        if log log_prove then fprintf logf "apply rule %s@\n" r.rule_name;
        r.rule_apply goal in
      let solve_subgoal = solve rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  if log log_prove then fprintf logf "@]";
  result

let solve_idfs min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@,@[<2>start idfs proving@\n";
  let solve = flip (solve rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@]@,@?";
  r

(* }}} *)
(* The top level interface. *) (* {{{ *)

let min_depth = 2
let max_depth = 3

let wrap_calculus f calculus =
  let rules = rules_of_calculus calculus in
  fun hypothesis conclusion ->
    f rules { Calculus.hypothesis; conclusion; frame = Expr.emp }

let is_entailment rules goal =
  let penalty { Calculus.hypothesis; conclusion; _ } =
    if Expr.equal hypothesis Expr.emp && Expr.equal conclusion Expr.emp
    then 0
    else Backtrack.max_penalty in
  let _, p = solve_idfs min_depth max_depth rules penalty goal in
  p = 0

let infer_frame rules goal =
  let penalty { Calculus.hypothesis; conclusion; _ } =
    if Expr.equal conclusion Expr.emp
    then Expr.size hypothesis
    else Backtrack.max_penalty in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then
    if ss = [] then [Expr.emp] else
    let f_of_sequent { Calculus.hypothesis; _ } = hypothesis in
    List.map f_of_sequent ss
  else []

let biabduct rules goal =
  let penalty { Calculus.hypothesis; conclusion; _ } =
    Expr.size hypothesis + Expr.size conclusion in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then
    if ss = [] then [{ frame = Expr.emp; antiframe = Expr.emp }] else
    let af_of_sequent { Calculus.hypothesis; conclusion; _ } =
      { frame = hypothesis; antiframe = conclusion } in
    List.map af_of_sequent ss
  else []

let is_entailment = wrap_calculus is_entailment
let infer_frame = wrap_calculus infer_frame
let biabduct = wrap_calculus biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent rules e = is_entailment rules e Expression.fls
(* }}} *)
