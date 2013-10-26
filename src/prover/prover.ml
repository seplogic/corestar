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

(* A root-leaf path of an expression must match ("or"?; "star"?; "not"?; OTHER).
The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
and "not". *)
(* NOTE: very inefficient; fix if profiler complains *)
let normalize e =
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
  let not_not _ = failwith "TODO" in
  let star_below_or _ = failwith "TODO" in
  let forbid _ = failwith "TODO" in
  let del_id _ = failwith "TODO" in
  let kill_unit _ = failwith "TODO" in
  let rec fix f e1 =
    let e2 = f e1 in
    if Expr.equal e1 e2 then e1 else fix f e2 in
  let fs =
    [ assoc { X.on = Expr.on_star; mk = Expr.mk_big_star }
    ; assoc { X.on = Expr.on_or; mk = Expr.mk_big_or }
    ; not_not
    ; star_below_or
(*     ; forbid Expr.on_not Expr.on_or *)
(*     ; forbid Expr.on_not Expr.on_star *)
    ; del_id Expr.on_star Expr.emp
    ; del_id Expr.on_or Expr.fls
    ; kill_unit Expr.on_or
    ; kill_unit Expr.on_star ] in
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
let normalize e =
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
	    | [x] -> List.map (fun m -> Done m) (find_matches bs (x, normalize e))
	    | ext_p::rest_p ->
	      begin
		let unspecific v =
		  let is_more (yes, no) =
		    let to_bind = normalize (mk_o yes) in
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
(* }}} *)


let rules_of_calculus _ = (* XXX *)
  [ id_rule ]

(* }}} *)
(* The main proof-search algorithm. *) (* {{{ *)

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with
with score [> Backtrack.max_penalty] needs a proof.  Anything in-between is kind
of acceptable as a leaf, but we should keep looking for something better.
  TODO: we may want min_penalty and max_penalty decrease with the level n
  TODO: we may want to count only once a leaf appearing twice
  TODO: we may want to partly cache the results of proving
*)
let rec solve rules penalty n goal =
  (* TODO: Add normalization here. *)
  let leaf = ([goal], penalty goal) in
  let result =
    if n = 0 then leaf else begin
      let process_rule r = r.rule_apply goal in
      let solve_subgoal = solve rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  result

let solve_idfs min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@,@[<2>start idfs proving";
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
    let f_of_sequent { Calculus.hypothesis; _ } = hypothesis in
    List.map f_of_sequent ss
  else []

let biabduct rules goal =
  let penalty { Calculus.hypothesis; conclusion; _ } =
    Expr.size hypothesis + Expr.size conclusion in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then
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
