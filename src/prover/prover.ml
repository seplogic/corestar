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

(* TODO: Move in [Corestar_std]? *)
let c0 x = x
let c1 x _ = x
let c2 x _ _ = x
let concatMap f xs = List.concat (List.map f xs)

let smt_is_valid a =
  Smt.push ();
  Smt.say (Expr.mk_not a);
  let r = match Smt.check_sat () with Smt.Unsat -> true | _ -> false in
  Smt.pop ();
  r

let is_pure e =
  let ok_n = [ Expr.on_star; Expr.on_or ] in
  let ok_2 = [ Expr.on_eq; Expr.on_neq ] in
  let ok_1 = [ Expr.on_not ] in
  let ok_0 = [ Expr.emp; Expr.fls ] in
  let stop_op = [ Expr.on_string_const; Expr.on_int_const ] in
  let rec is_ok e =
    let f _ _ = false in
    let f = List.fold_right ((|>) are_all_ok) ok_n f in
    let f = List.fold_right ((|>) (c2 true)) ok_2 f in
    let f = List.fold_right ((|>) is_ok) ok_1 f in
    let f = List.fold_right ((|>) (c1 true)) stop_op f in
    List.exists (Expr.equal e) ok_0 || Expr.cases (c1 true) f e
  and are_all_ok es = List.for_all is_ok es in
  is_ok e

(* True iff _x1=e1 * _x2=e2 * ... *)
let rec is_instantiation e =
(*   printf "oops@\n@?"; *)
  let is_lvar = Expr.cases Expr.is_lvar (c2 false) in
  let chk_eq f1 f2 = is_lvar f1 || is_lvar f2 in
  Expr.equal Expr.emp e
  || Expr.match_ e
    undefined (* shouldn't be called on terms *)
    ( Expr.on_star (List.for_all is_instantiation)
    & Expr.on_eq chk_eq
    & c2 false)

let is_true e =
  Expr.equal Expr.emp e
  || Expr.cases (c1 false) (Expr.on_eq Expr.equal & c2 false) e

let rec unfold on e =
  Expr.cases (c1 [e]) (on (concatMap (unfold on)) & c2 [e]) e

(* Removes zero, and removes repetitions of pure parts. *)
let ac_simplify_split is_zero on es =
  let xs = es >>= unfold on in
  let xs = List.filter (not @@ is_zero) xs in
  let xs, ys = List.partition is_pure xs in
  let module H = Hashtbl.Make (Expr) in
  let h = H.create (List.length xs) in
  List.iter (fun x -> H.replace h x ()) xs;
  (H.fold (fun x () xs -> x :: xs) h [], ys)

let ac_simplify is_zero on es =
  let xs, ys = ac_simplify_split is_zero on es in ys @ xs

let ac_make zero mk =
  function [] -> zero | [e] -> e | es -> mk es

let extract_pure_part e =
  let mk = ac_make Expr.emp Expr.mk_big_star in
  let xs, ys = ac_simplify_split is_true Expr.on_star [e] in
  (mk xs, mk ys)

let mk_big_star =
  ac_make Expr.emp Expr.mk_big_star @@ ac_simplify is_true Expr.on_star

let mk_big_or =
  let is_false = Expr.equal Expr.fls in
  ac_make Expr.fls Expr.mk_big_or @@ ac_simplify is_false Expr.on_or

let mk_star e1 e2 = mk_big_star [e1; e2]

let find_lvar_pvar_subs =
  let on_var_eq_var f g e =
    let not_on _ _ = g e in
    Expr.cases
      (fun _ -> g e)
      (Expr.on_eq
        (fun e1 e2 ->
	  Expr.cases
	    (fun v1 -> Expr.cases (fun v2 -> f v1 v2) not_on e2)
	    not_on e1)
	not_on) e in
  let add_if_good l =
    on_var_eq_var 
      (fun a b ->
	if Expr.is_lvar a && Expr.is_pvar b then (a, Expr.mk_var b)::l
	else if Expr.is_pvar a && Expr.is_lvar b then (b, Expr.mk_var a)::l
	else l)
      (fun _ -> l) in
  let get_subs = List.fold_left add_if_good [] in
  Expr.cases (fun _ -> []) (Expr.on_star get_subs (fun _ _ -> []))

(* Handles ss=[],
and caries over the pure parts of the antiframe into the frame. *)
let afs_of_sequents = function
  | [] -> [{ frame = Expr.emp; antiframe = Expr.emp }]
  | ss ->
      let f { Calculus.hypothesis; conclusion; _ } =
        let frame = hypothesis in
        let antiframe = conclusion in
        let pa, _ = extract_pure_part antiframe in
        let frame = mk_star frame pa in
        { frame; antiframe } in
      List.map f ss

let smt_implies a b =
  if is_pure b then
    let a_pure, _ = extract_pure_part a in
    smt_is_valid (Expr.mk_or (Expr.mk_not a_pure) b)
  else false

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
    (function { Calculus.hypothesis; conclusion; frame } ->
      if smt_implies hypothesis conclusion
      then [[{ Calculus.hypothesis; conclusion = Expr.emp; frame}]] else []) }

let inline_pvars_rule =
  { rule_name = "substitution (of logical vars with program vars)"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let subs = find_lvar_pvar_subs hypothesis in
      let sub_hyp = Expr.substitute subs hypothesis in
      let mk_eq (a, b) = Expr.mk_eq (Expr.mk_var a) b in
      let hyp = mk_big_star (sub_hyp :: List.map mk_eq subs) in
      [[{ Calculus.hypothesis = hyp; conclusion; frame}]]) }

(* A root-leaf path of the result matches ("or"?; "star"?; "not"?; OTHER).
The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
and "not". *)
let normalize =
  let rec not_not e =
    let e = Expr.cases (c1 e) (Expr.recurse not_not) e in
    let negate e =
      let ne = Expr.mk_not e in
      Expr.cases (c1 ne) (Expr.on_not c0 & c2 ne) e in
    Expr.cases (c1 e) (Expr.on_not negate & c2 e) e in
  let rec star_below_or e = (* (a∨b)*(c∨d) becomes (a*c)∨(a*d)∨(b*c)∨(b*d) *)
    let ess = List.map (unfold Expr.on_or) (unfold Expr.on_star e) in
    let fss = Misc.product ess in
    let r f = if Expr.equal f e then f else star_below_or f in
    let fs = List.map (r @@ mk_big_star) fss in
    mk_big_or fs in
  let rec forbid_not on e = (* assert that "not" doesn't appear on top of [on] *)
    let chk1 e =
      Expr.cases (c1 ()) (on (fun _ -> assert false) & c2 ()) e;
      ignore (forbid_not on e) in
    let chk = ignore @@ forbid_not on in
    Expr.cases (c1 ()) (Expr.on_not chk1 & fun _ -> List.iter chk) e; e in
  let fs =
    [ not_not
    ; star_below_or
    ; forbid_not Expr.on_or
    ; forbid_not Expr.on_star ] in
  List.fold_left (@@) id fs

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
   They are not, as normalize_comassoc would not do the right thing on them
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
  Expr.cases (c1 e) (on_comassoc unfold (c2 e)) e

type match_result =
  | Done of bindings
  | More of bindings * (Expr.t * Expr.t)

(*
  Expr.t -> Expr.t -> bindings list
  Assumes that e does not contain pattern variables

  input bs is one assignment, the current branch we are exploring
  output is list of assignments, all possible extensions which leads to a match

  Parameterized by [can_match] : var -> exp -> bool
  TODO: needs also an [is_free] : var -> bool, signifying which variables should be instantiated
*)
let rec find_matches can_match bs (p, e) =
  let bind pv =
    begin
      match try_find pv bs with
	| None -> [Done (StringMap.add pv e bs)]
	| Some oe -> if e = oe then [Done bs] else []
    end in
  let on_pvar pv e = if can_match pv e then bind pv else [] in
  let on_pop_var _ _ _ = [] in
  let on_pop_op po ps o es =
    if po <> o then []
    else
      let handle_comassoc _ _ =
	begin
	  let mk_o l = Expr.mk_app o l in
	  match ps with
	    | [] -> [Done bs]
	    | [x] -> List.map (fun m -> Done m) (find_matches can_match bs (x, normalize_comassoc e))
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
		    | [x] -> List.map (fun m -> Done m) (find_matches can_match bs (ext_p, x))
		    | _ ->
		      let ext_match (ext_e, rest_e) =
			let mk_more m = More (m, (mk_o rest_p, mk_o rest_e)) in
			List.map mk_more (find_matches can_match bs (ext_p, ext_e)) in
		      unique_extractions es >>= ext_match in
		Expr.cases
		  (fun v -> if Expr.is_tpat v then unspecific v else specific ())
		  (fun _ _ -> specific ())
		  ext_p
	      end
	end in
      let handle_skew so _ =
	if List.length ps <> List.length es then []
	else
	  let todos = List.combine ps es in
	  let process_todo acc (tp, te) =
	    acc >>= (flip (find_matches can_match) (tp, te)) in
	  let result = List.fold_left process_todo [bs] todos in
	  List.map (fun r -> Done r) result in
      on_comassoc handle_comassoc handle_skew po ps in
  let matches =
    Expr.cases (fun pv -> on_pvar pv e) (fun po ps -> Expr.cases (on_pop_var po ps) (on_pop_op po ps) e) p in
  let process_match = function
    | Done final_bs -> [final_bs]
    | More (next_bs, next_pair) ->
      (*      Format.printf "<processing more %d>" (List.length next_bs); *)
      find_matches can_match next_bs next_pair in
  matches >>= process_match

(* interpret free variables as existential variables *)
let find_existential_matches =
  find_matches (fun pv e -> if Expr.is_lvar pv then true else Expr.cases ((=) pv) (fun _ _ -> false) e)

let spatial_id_rule =
  { rule_name = "spatial parts match"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      if log log_prove then fprintf logf "hp: %a@,hs: %a@,cp: %a@,cs: %a"
	Expr.pp hyp_pure Expr.pp hyp_spatial Expr.pp conc_pure Expr.pp conc_spatial;
      if Expr.equal hyp_spatial conc_spatial (* should really be handled by matching *)
      then [[{ Calculus.hypothesis = hyp_pure; conclusion = conc_pure; frame}]] else
      let matches = find_existential_matches StringMap.empty (conc_spatial, hyp_spatial) in
      if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
      let mk_goal m =
	let b = StringMap.bindings m in
	let mk_eq (v, e) = Expr.mk_eq (Expr.mk_var v) e in
	[ { Calculus.hypothesis = hyp_pure
	  ; conclusion = mk_big_star (conc_pure :: List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

let find_pattern_matches =
  find_matches (fun v -> let b = Expr.is_tpat v in Expr.cases (fun _ -> true) (fun _ _ -> b))

let find_sequent_matches bs ps s =
  let fm pat exp bs = find_pattern_matches bs (pat, exp) in
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
  id_rule
  :: smt_pure_rule
  :: inline_pvars_rule
  :: spatial_id_rule
  :: List.map to_rule c

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
  if log log_prove then fprintf logf "goal: %a@," CalculusOps.pp_sequent goal;
  let leaf = ([goal], penalty n goal) in
  if log log_prove then fprintf logf "Current goal has penalty %d at level %d@\n" (penalty n goal) n;
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
  let penalty _ { Calculus.hypothesis; conclusion; _ } =
    (* TODO: Should also require that the hypothesis is pure? *)
    if is_instantiation conclusion
    then 0
    else Backtrack.max_penalty in
  let _, p = solve_idfs min_depth max_depth rules penalty goal in
  p = 0

let infer_frame rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    if is_instantiation conclusion
    then (n + 1) * (Expr.size hypothesis)
    else Backtrack.max_penalty in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let biabduct rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    (n + 1) * (Expr.size hypothesis + Expr.size conclusion) in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let is_entailment = wrap_calculus is_entailment
let infer_frame = wrap_calculus infer_frame
let biabduct = wrap_calculus biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent rules e =
  is_entailment rules e Expr.fls
(* }}} *)
