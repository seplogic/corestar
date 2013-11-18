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
    & Expr.on_neq chk_eq
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

(* HACK: Simplified version of [Symexec.update_defs], used for
[guess_instance] below. See that guy's comment. *)
let get_defs vs =
  let is_v =
    flip StringSet.mem (List.fold_right StringSet.add vs StringSet.empty) in
  let is_ve = Expr.cases is_v (c2 false) in
  let rec is_v_free e =
    Expr.match_ e (not @@ is_v) (c1 (List.for_all is_v_free)) in
  let rec f acc =
    let eq acc a b =
      let va, vb = is_ve a, is_ve b in
      if va || vb then begin
        let v, e = if va then Expr.bk_var a, b else Expr.bk_var b, a in
        if is_v_free e then StringMap.add v e acc else acc
      end else acc in
    Expr.cases undefined
      ( Expr.on_eq (eq acc)
      & Expr.on_star (List.fold_left f acc)
      & (c2 acc) ) in
  f StringMap.empty

(* TODO: This is a complete hack. Should be replaced by something else,
for example a search based on models returned by Z3. Also, it repeats code in
[Symexec]. *)
let guess_instance vs e f =
  let eds = get_defs vs e in
  let fds = get_defs vs f in
  let mk_eq x =
    try
      let v = StringMap.find x eds in
      let w = StringMap.find x fds in
      [Expr.mk_eq v w]
    with Not_found -> [] in
  let eqs = vs >>= mk_eq in
  mk_big_star eqs

let rec all_pairs = function
  | [] -> []
  | x :: xs -> List.map (fun y -> (x,y)) xs @ all_pairs xs

let get_lvars acc e =
  let vs = List.filter Expr.is_lvar (Expr.vars e) in
  List.fold_right StringSet.add vs acc

let smt_implies e f = smt_is_valid (Expr.mk_or (Expr.mk_not e) f)

let shuffle ls = ls (* XXX *)

let dbg_mc = ref 0

(* HACK. To fix. *)
let smt_abduce hypothesis conclusion =
  if is_pure conclusion then begin
    (* XXX: this is intuitionistic *)
    let pure_hypothesis, _ = extract_pure_part hypothesis in
    let rec shrink eqs =
      incr dbg_mc;
      printf "@[@<2>shrink %d@ %a@]@\n" !dbg_mc (pp_list_sep " * " Expr.pp) eqs;
      Smt.log_comment (string_of_int !dbg_mc);
      if smt_implies (mk_big_star (pure_hypothesis :: eqs)) conclusion
      then begin
        let rec f xs y zs = match shrink (xs @ zs) with
          | Some _ as r  -> r
          | None -> (match zs with
            | [] -> Some (Expr.mk_big_star eqs)
            | z :: zs -> f (y :: xs) z zs) in
        (match eqs with [] -> Some Expr.emp | x :: xs -> f [] x xs)
      end else None in
    let rec grow xs = function
      | [] -> xs
      | y :: ys ->
          if smt_implies (mk_big_star (pure_hypothesis :: y :: xs)) Expr.fls
          then grow xs ys else grow (y :: xs) ys in
    let cs = unfold Expr.on_star conclusion in
    let r = shrink (grow [] cs) in
    (match r with
    | Some e -> Smt.log_comment "here"; printf "@[<2>smt abduced@ %a@]@\n" Expr.pp e
    | None -> ());
    r
  end else None
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

let or_rule =
  { rule_name = "or elimination"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let mk_goal c = [ { Calculus.hypothesis; conclusion = c; frame } ] in
      Expr.cases (c1 []) (Expr.on_or (List.map mk_goal) (c2 [])) conclusion) }

let smt_pure_rule =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      (match smt_abduce hypothesis conclusion with
      | None -> []
      | Some conclusion -> [[{ Calculus.hypothesis; conclusion; frame }]])) }

(* TODO(rg): I don't understand why this rule isn't too specific. *)
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

  Parameterized by [is_free] : var -> bool, signifying which variables should be instantiated
  and [can_be_op] : var -> bool, signifying which variables can be instantiated not just with variables
*)

let rec find_matches is_free can_be_op bs (p, e) =
  let also_match = find_matches is_free can_be_op in
  let bind pv =
    begin
      match try_find pv bs with
	| None -> [Done (StringMap.add pv e bs)]
	| Some oe -> if e = oe then [Done bs] else []
    end in
  let on_pvar_var pv ev = if is_free pv then bind pv else if pv = ev then [Done bs] else [] in
  let on_pvar_op pv o es = if can_be_op pv then bind pv else [] in
  let on_pop_var _ _ _ = [] in
  let on_pop_op po ps o es =
    if po <> o then []
    else
      let handle_comassoc _ _ =
	begin
	  let mk_o l = Expr.mk_app o l in
	  match ps with
	    | [] -> if es = [] then [Done bs] else []
	    | [x] -> List.map (fun m -> Done m) (also_match bs (x, normalize_comassoc e))
	    | ext_p::rest_p ->
	      begin
		let unspecific v =
		  let is_more (yes, no) =
		    let to_bind = normalize_comassoc (mk_o yes) in
		    match try_find v bs with
		      | None ->
			Some (More (StringMap.add v to_bind bs, (mk_o rest_p, mk_o no)))
		      | Some oyes ->
			if oyes = to_bind then Some (More (bs, (mk_o rest_p, mk_o no)))
			else None in
		  unique_subsets es |> map_option is_more in
		let specific () =
		  match es with
		    | [] -> []
		    | [x] -> if rest_p = [] then List.map (fun m -> Done m) (also_match bs (ext_p, x)) else []
		    | _ ->
		      let ext_match (ext_e, rest_e) =
			let mk_more m = More (m, (mk_o rest_p, mk_o rest_e)) in
			List.map mk_more (also_match bs (ext_p, ext_e)) in
		      unique_extractions es >>= ext_match in
		Expr.cases
		  (fun v -> if can_be_op v then unspecific v else specific ())
		  (fun _ _ -> specific ())
		  ext_p
	      end
	end in
      let handle_skew so _ =
	if List.length ps <> List.length es then []
	else
	  let todos = List.combine ps es in
	  let process_todo acc (tp, te) =
	    acc >>= (flip also_match (tp, te)) in
	  let result = List.fold_left process_todo [bs] todos in
	  List.map (fun r -> Done r) result in
      on_comassoc handle_comassoc handle_skew po ps in
  let matches = cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) in
  let process_match = function
    | Done final_bs -> [final_bs]
    | More (next_bs, next_pair) -> also_match next_bs next_pair in
  matches >>= process_match
  
(*
let rec find_some f = function
  | [] -> None
  | h :: t -> ( match f h with None -> find_some f t | x -> x )

(* [can_convert} : var -> bool says if a variable can be instantiated *)
let rec find_conversion can_convert bs (p, e) =
  printf "@\nconvert (%a,%a)@\n" Expr.pp p Expr.pp e;
  let bind pv =
    printf "@\nTrying to bind %s to %a@\n" pv Expr.pp e;
    match try_find pv bs with
      | None -> Some (StringMap.add pv e bs)
      | Some oe -> if e = oe then Some bs else None in
  let on_pvar pv =
    if can_convert pv
    then Expr.cases (c1 (bind pv)) (c2 None) e
    else if Expr.equal p e then Some bs else None in
  let on_op po ps =
    Expr.cases
      (c1 None)
      (fun o es -> if o <> po || List.length es <> List.length ps then None else
	  let handle_comassoc _ _ =
	    let rec inner bs = function
	      | [], _ -> Some bs
	      | ph :: pt, es ->
		option
		  None
		  (fun (bs, rest_e) -> inner bs (pt, rest_e))
		  (find_some
		     (fun (ext_e,rest_e) -> option_map (fun m -> (m, rest_e))
		       (find_conversion can_convert bs (ext_e, ph)))
		     (unique_extractions es)) in
	    inner bs (ps,es) in
	  let handle_skew _ _ =
	    let rec inner bs = function
	    | [] -> Some bs
	    | h :: t -> option None (flip inner t) (find_conversion can_convert bs h) in
	    inner bs (List.combine ps es) in
	  on_comassoc handle_comassoc handle_skew po ps
      ) e in
  Expr.cases on_pvar on_op p
*)

(* interpret free variables as existential variables *)
let find_existential_matches =
  find_matches Expr.is_lvar (c1 false)

let find_existential_sub_matches leftover_var =
  find_matches Expr.is_lvar ((=) leftover_var)

(*
let find_existential_match = find_conversion Expr.is_lvar
*)

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

let match_rule =
  { rule_name = "matching free variables"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let matches =
	  find_existential_matches StringMap.empty (conclusion, hypothesis) in
      if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
      let mk_goal m =
	let b = StringMap.bindings m in
	let mk_eq (v, e) = Expr.mk_eq (Expr.mk_var v) e in
	[ { Calculus.hypothesis = hypothesis
	  ; conclusion = mk_big_star (List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

(* This rule is not in the list yet *)
let match_subformula_rule =
  { rule_name = "matching subformula"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let lo_name = "_leftover" in
      let leftover = Expr.mk_var lo_name in
      printf "leftover is lvar: %b" (Expr.is_lvar lo_name);
      let enhanced_conc = mk_star leftover conclusion in
      let matches =
	find_existential_sub_matches lo_name StringMap.empty (enhanced_conc, hypothesis) in
      if log log_prove then fprintf logf "@,trying to match %a and % a@," Expr.pp enhanced_conc Expr.pp hypothesis;
      if log log_prove then
	fprintf logf "@,@[<v 2>found %d matches:@,%a@,@]"
	  (List.length matches)
	  (pp_list_sep "\n" (fun f m -> fprintf f "[ %a ]" (pp_list_sep "; " (fun f (v,e) -> fprintf f "%s->%a" v Expr.pp e)) (StringMap.bindings m))) matches;
      let mk_goal m =
	let leftover_match = StringMap.find lo_name m in
	if is_pure leftover_match then
	  let m = StringMap.remove lo_name m in
          let b = StringMap.bindings m in
	  let mk_eq (v, e) = Expr.mk_eq (Expr.mk_var v) e in
	  [ [ { Calculus.hypothesis = hypothesis
	    ; conclusion = mk_big_star (List.map mk_eq b)
	    ; frame } ] ]
	else [] in
      matches >>= mk_goal) }

let find_pattern_matches = find_matches (c1 true) Expr.is_tpat

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
  :: or_rule
(*  :: match_rule *)
(*  :: match_subformula_rule *)
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
  if log log_prove then fprintf logf "@[<2>@{<details>";
  let goal =
    { Calculus.frame = normalize frame
    ; hypothesis = normalize hypothesis
    ; conclusion = normalize conclusion } in
  if log log_prove then fprintf logf "@{<summary>goal:@}@,@{<p>%a@}@," CalculusOps.pp_sequent goal;
  let leaf = ([goal], penalty n goal) in
  if log log_prove then fprintf logf "@{<p>Current goal has penalty %d at level %d@}@\n" (penalty n goal) n;
  let result =
    if n = 0 then leaf else begin
      let process_rule r =
        if log log_prove then fprintf logf "@{<p>apply rule %s@}@\n" r.rule_name;
        r.rule_apply goal in
      let solve_subgoal = solve rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  if log log_prove then fprintf logf "@}@]";
  result

let solve_idfs min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@,@[<2>@{<details>@{<summary>start idfs proving@}@\n";
  let solve = flip (solve rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@}@]@,@?";
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
    then
      let _, hyp_spatial = extract_pure_part hypothesis in
      (n + 1) * (Expr.size hyp_spatial)
    else Backtrack.max_penalty in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let biabduct rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    let _, hyp_spatial = extract_pure_part hypothesis in
    let _, con_spatial = extract_pure_part conclusion in
    (n + 1) * (Expr.size hyp_spatial + Expr.size con_spatial) in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let is_entailment = wrap_calculus is_entailment
let infer_frame = wrap_calculus infer_frame
let biabduct = wrap_calculus biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent rules e =
  is_entailment rules e Expr.fls
(* }}} *)
