(* Modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

(* }}} *)

let z3_ctx = Syntax.z3_ctx

type frame_and_antiframe =
  { frame : Z3.Expr.expr
  ; antiframe : Z3.Expr.expr }

(* Helper functions for prover rules. *) (* {{{ *)

let smt_is_valid a =
  Smt.push ();
  Smt.say (Z3.Boolean.mk_not z3_ctx a);
  let r = Smt.check_sat () = Smt.Unsat in
  Smt.pop ();
  r

(* True iff _x1=e1 * _x2=e2 * ... *)
let rec is_instantiation e =
(*   printf "oops@\n@?"; *)
  let chk_eq f1 f2 = Syntax.is_lvar f1 || Syntax.is_lvar f2 in
  let chk_distinct f = List.fold_left (fun b e -> b || Syntax.is_lvar e) true f in
  (Syntax.on_emp (c1 true)
   & Syntax.on_star (fun a b -> is_instantiation a && is_instantiation b)
   & Syntax.on_eq chk_eq
   & Syntax.on_distinct chk_distinct
   & c1 false) e

let is_true e =
  (Syntax.on_emp (c1 true)
   & Syntax.on_eq Syntax.expr_equal
   & c1 false) e

let rec unfold on e =
  (Syntax.on_var (c1 [e])
   & (on (ListH.concatMap (unfold on)) & c1 [e]))
    e

(* Removes zero, and removes repetitions of pure parts.
Returns (pure, spatial) pair. *)
let ac_simplify_split is_zero on es =
  let xs = es >>= unfold on in
  let xs = List.filter (not @@ is_zero) xs in
  let xs, ys = List.partition Syntax.is_pure xs in
  let h = Syntax.ExprHashSet.create (List.length xs) in
  List.iter (fun x -> Syntax.ExprHashSet.add h x) xs;
  (Syntax.ExprHashSet.fold (fun x xs -> x :: xs) h [], ys)

let ac_simplify is_zero on es =
  let xs, ys = ac_simplify_split is_zero on es in ys @ xs

let ac_make zero mk =
  function [] -> zero | [e] -> e | es -> mk es

(* Returns (pure, spatial) pair. *)
let extract_pure_part e =
  let mk = ac_make Syntax.mk_emp Syntax.mk_big_star in
  let xs, ys = ac_simplify_split is_true Syntax.on_big_star [e] in
  (mk xs, mk ys)

let mk_big_star l =
  (ac_make Syntax.mk_emp Syntax.mk_big_star @@ ac_simplify is_true Syntax.on_big_star) l

let mk_big_or =
  ac_make (Z3.Boolean.mk_false z3_ctx) (Z3.Boolean.mk_or z3_ctx) @@
    ac_simplify Z3.Expr.is_false Syntax.on_or

let mk_star e1 e2 = mk_big_star [e1; e2]
let mk_or e1 e2 = mk_big_or [e1; e2]

let mk_meet e1 e2 =
  let e1p, e1s = extract_pure_part e1 in
  let e2p, e2s = extract_pure_part e2 in
  if not (Syntax.expr_equal e1s Syntax.mk_emp && Syntax.expr_equal e2s Syntax.mk_emp)
  then (Z3.Boolean.mk_false z3_ctx) (* TODO: More precise. *)
  else mk_star e1p e2p

let mk_big_meet = function
  | [] -> Syntax.mk_emp
  | [e] -> e
  | e :: es -> List.fold_left mk_meet e es

(* TODO(rg): Add a comment with what this does. *)
let find_lvar_pvar_subs e =
  let add_if_good l =
    Syntax.on_eq
      (fun a b ->
	if Syntax.is_lvar a && Syntax.is_pvar b then (a, b)::l
	else if Syntax.is_pvar a && Syntax.is_lvar b then (b, a)::l
	else l)
    & (c1 l) in
  let get_subs = List.fold_left add_if_good [] in
  (Syntax.on_big_star get_subs (fun _ -> [])) e

(* Handles ss=[],
and caries over the pure parts of the antiframe into the frame. *)
let afs_of_sequents = function
  | [] -> [{ frame = Syntax.mk_emp; antiframe = Syntax.mk_emp }]
  | ss ->
      let f { Calculus.hypothesis; conclusion; _ } =
        let frame = hypothesis in
        let antiframe = conclusion in
        let pa, _ = extract_pure_part antiframe in
        let frame = mk_star frame pa in
        { frame; antiframe } in
      List.map f ss

(* Should find some lvar that occurs only on the right and return some good
candidates to which it might be equal. Dumb, for now: all (maximal) terms that
occur in equalities. *)
let guess_instance e f =
  let get_lvars e =
    let vs = List.filter Syntax.is_lvar (Syntax.vars e) in
    List.fold_right Syntax.ExprSet.add vs Syntax.ExprSet.empty in
  let get_eq_args e =
    let h = Syntax.ExprHashSet.create 0 in
    let rec get e =
      ( Syntax.on_big_star (List.iter get)
      & Syntax.on_or (List.iter get)
      & Syntax.on_eq (fun a b -> Syntax.ExprHashSet.add h a; Syntax.ExprHashSet.add h b)
      & Syntax.on_app (c2 ()) ) e in
    get e;
    Syntax.ExprHashSet.fold (fun x xs -> x :: xs) h [] in
  try
    let v = Syntax.ExprSet.choose (Syntax.ExprSet.diff (get_lvars f) (get_lvars e)) in
    let es = get_eq_args e in
    List.map (fun e -> (v, e)) es
  with Not_found -> []

let smt_implies e f = smt_is_valid (Z3.Boolean.mk_or z3_ctx [Z3.Boolean.mk_not z3_ctx e; f])

let shuffle ls = ls (* XXX *)

let dbg_mc = ref 0

(* HACK. To fix. Also, profiling showed this is extremely slow. *)
let smt_abduce hypothesis conclusion =
  if Syntax.is_pure conclusion then begin
    (* XXX: this is intuitionistic *)
    let pure_hypothesis, _ = extract_pure_part hypothesis in
    let rec shrink eqs =
      printf "shrink %d@\n@?" (List.length eqs);
(* DBG
      incr dbg_mc;
      printf "@[@<2>shrink %d@ %a@]@\n" !dbg_mc (pp_list_sep " * " Syntax.pp) eqs;
      Smt.log_comment (string_of_int !dbg_mc);
      *)
      if smt_implies (mk_big_star (pure_hypothesis :: eqs)) conclusion
      then begin
        let rec f xs y zs = match shrink (xs @ zs) with
          | Some _ as r  -> r
          | None -> (match zs with
            | [] -> Some (Syntax.mk_big_star eqs)
            | z :: zs -> f (y :: xs) z zs) in
        (match eqs with [] -> Some Syntax.mk_emp | x :: xs -> f [] x xs)
      end else None in
    let rec grow xs = function
      | [] -> xs
      | (y :: ys) as yys ->
          printf "DBG grow, left %d@\n@?" (List.length yys);
          if smt_implies (mk_big_star (pure_hypothesis :: y :: xs)) (Z3.Boolean.mk_false z3_ctx)
          then grow xs ys else grow (y :: xs) ys in
    let cs = unfold Syntax.on_big_star conclusion in
    let r = if List.length cs > 10 then None else shrink (grow [] cs) in
    (* DBG
    (match r with
    | Some e -> Smt.log_comment "here"; printf "@[<2>smt abduced@ %a@]@\n" Expr.pp e
    | None -> ()); *)
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
      if Syntax.expr_equal hypothesis conclusion then [[]] else []) }

let or_rule =
  { rule_name = "or elimination"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let mk_goal c = [ { Calculus.hypothesis; conclusion = c; frame } ] in
      (Syntax.on_or (List.map mk_goal) & (c1 [])) conclusion) }

let smt_pure_rule =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      (if smt_implies hypothesis conclusion
      then [[{ Calculus.hypothesis; conclusion = Syntax.mk_emp; frame }]] else [])) }

(* ( H ⊢ C ) if ( ⊢ x=e and H * x=e ⊢ C ) *)
(* TODO(rg): activating this makes it spin forever. Why?*)
let abduce_instance_rule =
  { rule_name = "guess value of lvar that occurs only on rhs"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let gs = guess_instance hypothesis conclusion in
      let mk (x, e) =
        let eq = Z3.Boolean.mk_eq z3_ctx x e in
        [ { Calculus.hypothesis = Syntax.mk_emp; conclusion = eq; frame = Syntax.mk_emp }
        ; { Calculus.hypothesis = mk_star hypothesis eq; conclusion; frame } ]
      in
      List.map mk gs) }

(* TODO(rg): I don't understand why this rule isn't too specific. *)
let inline_pvars_rule =
  { rule_name = "substitution (of logical vars with program vars)"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let subs = find_lvar_pvar_subs hypothesis in
      let (subees, subers) = List.split subs in
      let sub_hyp = Z3.Expr.substitute hypothesis subees subers in
      let mk_eq (a, b) = Z3.Boolean.mk_eq z3_ctx a b in
      let hyp = mk_big_star (sub_hyp :: List.map mk_eq subs) in
      [[{ Calculus.hypothesis = hyp; conclusion; frame}]]) }

(* A root-leaf path of the result matches ("or"?; "star"?; "not"?; OTHER).
The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
and "not". *)
let normalize =
  let rec not_not e =
    let e = (Syntax.on_var (c1 e)
             & Syntax.on_app (Syntax.recurse not_not)) e in
    let negate e =
      let ne = Z3.Boolean.mk_not z3_ctx e in
      (Syntax.on_not c0 & c1 ne) e in
    (Syntax.on_not negate & c1 e) e in
  let rec star_below_or e = (* (a∨b)*(c∨d) becomes (a*c)∨(a*d)∨(b*c)∨(b*d) *)
    let ess = List.map (unfold Syntax.on_or) (unfold Syntax.on_big_star e) in
    let fss = Misc.product ess in
    let r f = if Syntax.expr_equal f e then f else star_below_or f in
    let fs = List.map (r @@ mk_big_star) fss in
    mk_big_or fs in
  let rec forbid_not on e = (* assert that "not" doesn't appear on top of [on] *)
    let chk1 e =
      (on (fun _ -> assert false) & c1 ()) e;
      ignore (forbid_not on e) in
    let chk = ignore @@ forbid_not on in
    (Syntax.on_not chk1
     & Syntax.on_app (fun _ -> List.iter chk)) e; e in
  let fs =
    [ not_not
    ; star_below_or
    ; forbid_not Syntax.on_or
    ; forbid_not Syntax.on_star ] in
  List.fold_left (@@) id fs

(* find_matches and helpers *) (* {{{ *)
let unique_extractions l =
  let rec inner acc = function
    | [] -> []
    | x::xs ->
      let rest = (List.map (fun (y, ys) -> (y, x::ys)) (inner (x::acc) xs)) in
      if List.exists (Syntax.expr_equal x) acc then rest
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
      if List.exists (Syntax.expr_equal x) acc then inner (x::acc) xs
      else
	inner [x] xs >>= (fun (yes, no) -> splits acc |> List.map (fun (to_yes, to_no) -> (to_yes@yes, to_no@no))) in
  inner [] l


type bindings = Z3.Expr.expr Syntax.ExprMap.t

let try_find x m = try Some (Syntax.ExprMap.find x m) with Not_found -> None

let cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) =
  let on_pvar pv = (Syntax.on_var (on_pvar_var pv) & Syntax.on_app (on_pvar_op pv)) e in
  let on_pop po ps = (Syntax.on_var (on_pop_var po ps) & Syntax.on_app (on_pop_op po ps)) e in
  (Syntax.on_var on_pvar & Syntax.on_app on_pop) p

(* Not needed as eq and neq are not comassoc
   They are not, as normalize_comassoc would not do the right thing on them
let on_pair f a b = f [a; b]
*)

let on_comassoc handle_comassoc handle_skew e =
  ( Syntax.on_big_star handle_comassoc
  & Syntax.on_or handle_comassoc
(*
  & Expr.on_eq (on_pair handle_comassoc)
  & Expr.on_neq (on_pair handle_comassoc)
*)
  & handle_skew )
  e

(*
  This normalization is needed in the matcher
  because the matcher implicitly applies it to the pattern
  it has to be done also to the expression in order to obtain a match
*)
let normalize_comassoc e =
  let unfold = function [x] -> x | _ -> e in
  (on_comassoc unfold (c1 e)) e

type match_result =
  | Done of bindings
  | More of bindings * (Z3.Expr.expr * Z3.Expr.expr)

(*
  Z3.Expr.expr -> Z3.Expr.expr -> bindings list
  Assumes that [e] does not contain pattern variables

  input [bs] is one assignment, the current branch we are exploring
  output is list of assignments, all possible extensions which leads to a match

  Parameterized by [is_free] : expr -> bool, signifying which variables should be instantiated
  and [can_be_op] : expr -> bool, signifying which variables can be instantiated not just with variables
*)

let rec find_matches is_free can_be_op bs (p, e) =
  let also_match = find_matches is_free can_be_op in
  let bind pv =
    begin
      match try_find pv bs with
	| None -> [Done (Syntax.ExprMap.add pv e bs)]
	| Some oe -> if Syntax.expr_equal e oe then [Done bs] else []
    end in
  let on_pvar_var pv ev = if is_free pv then bind pv else if Syntax.expr_equal pv ev then [Done bs] else [] in
  let on_pvar_op pv o es = if can_be_op pv then bind pv else [] in
  let on_pop_var _ _ _ = [] in
  let on_pop_op po ps o es =
    if not (Z3.FuncDecl.equal po o) then []
    else
      let handle_comassoc _ =
	begin
	  let mk_o l =
	    (* this is a hack to avoid creating invalid Z3
	       expressions: '*' is a binary operation as far as Z3 is
	       concerned, so it can only be applied to arbitrary lists
	       of elements via mk_big_star *)
	    if Z3.FuncDecl.equal o Syntax.star then mk_big_star l
	    else Z3.FuncDecl.apply o l in
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
		    Some (More (Syntax.ExprMap.add v to_bind bs, (mk_o rest_p, mk_o no)))
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
	      (Syntax.on_var
		 (fun v -> if can_be_op v then unspecific v else specific ())
	       & (fun _ -> specific ()))
		ext_p
	    end
	end in
      let handle_skew _ =
	if List.length ps <> List.length es then []
	else
	  let todos = List.combine ps es in
	  let process_todo acc (tp, te) =
	    acc >>= (flip also_match (tp, te)) in
	  let result = List.fold_left process_todo [bs] todos in
	  List.map (fun r -> Done r) result in
      on_comassoc handle_comassoc handle_skew (Z3.FuncDecl.apply po ps) in
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
  printf "@\nconvert (%a,%a)@\n" Syntax.pp_expr p Syntax.pp_expr e;
  let bind pv =
    printf "@\nTrying to bind %s to %a@\n" pv Syntax.pp_expr e;
    match try_find pv bs with
      | None -> Some (StringMap.add pv e bs)
      | Some oe -> if e = oe then Some bs else None in
  let on_pvar pv =
    if can_convert pv
    then Syntax.cases (c1 (bind pv)) (c2 None) e
    else if Syntax.expr_equal p e then Some bs else None in
  let on_op po ps =
    Syntax.cases
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
  Syntax.cases on_pvar on_op p
*)

(* interpret free variables as existential variables *)
let find_existential_matches =
  find_matches Syntax.is_lvar (c1 false)

let find_existential_sub_matches leftover_var =
  find_matches Syntax.is_lvar (Syntax.expr_equal leftover_var)

(*
let find_existential_match = find_conversion Syntax.is_lvar
*)

let spatial_id_rule =
  { rule_name = "spatial parts match"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      if log log_prove then fprintf logf "hp: %a@,hs: %a@,cp: %a@,cs: %a"
	Syntax.pp_expr hyp_pure Syntax.pp_expr hyp_spatial Syntax.pp_expr conc_pure Syntax.pp_expr conc_spatial;
      if Syntax.expr_equal hyp_spatial conc_spatial (* should really be handled by matching *)
      then [[{ Calculus.hypothesis = hyp_pure; conclusion = conc_pure; frame}]] else
      let matches = find_existential_matches Syntax.ExprMap.empty (conc_spatial, hyp_spatial) in
      if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
      let mk_goal m =
	let b = Syntax.ExprMap.bindings m in
	let mk_eq (v, e) = Z3.Boolean.mk_eq z3_ctx v e in
	[ { Calculus.hypothesis = hyp_pure
	  ; conclusion = mk_big_star (conc_pure :: List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

let match_rule =
  { rule_name = "matching free variables"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let matches =
	  find_existential_matches Syntax.ExprMap.empty (conclusion, hypothesis) in
      if log log_prove then fprintf logf "@,found %d matches@\n" (List.length matches);
      let mk_goal m =
	let b = Syntax.ExprMap.bindings m in
	let mk_eq (v, e) = Z3.Boolean.mk_eq z3_ctx v e in
	[ { Calculus.hypothesis = hypothesis
	  ; conclusion = mk_big_star (List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

let match_subformula_rule =
  { rule_name = "matching subformula"
  ; rule_apply =
    (function { Calculus.hypothesis; conclusion; frame } ->
      let lo_name = "_leftover" in
      let leftover = Z3.Expr.mk_const_s z3_ctx lo_name (Z3.Boolean.mk_sort z3_ctx) in
      (* printf "leftover is lvar: %b" (Syntax.is_lvar leftover); *)
      let enhanced_conc = Syntax.mk_star leftover conclusion in
      let matches =
	find_existential_sub_matches leftover Syntax.ExprMap.empty (enhanced_conc, hypothesis) in
      if log log_prove then fprintf logf "@,trying to match %a and % a@," Syntax.pp_expr enhanced_conc Syntax.pp_expr hypothesis;
      if log log_prove then
	fprintf logf "@,@[<v 2>found %d matches:@,%a@,@]"
	  (List.length matches)
	  (pp_list_sep "\n" (fun f m -> fprintf f "[ %a ]" (pp_list_sep "; " (fun f (v,e) -> fprintf f "%a->%a" Syntax.pp_expr v Syntax.pp_expr e)) (Syntax.ExprMap.bindings m))) matches;
      let mk_goal m =
	let leftover_match = Syntax.ExprMap.find leftover m in
	if Syntax.is_pure leftover_match then
	  let m = Syntax.ExprMap.remove leftover m in
          let b = Syntax.ExprMap.bindings m in
	  let mk_eq (v, e) = Z3.Boolean.mk_eq z3_ctx v e in
	  [ [ { Calculus.hypothesis = hypothesis
	    ; conclusion = mk_big_star (List.map mk_eq b)
	    ; frame } ] ]
	else [] in
      matches >>= mk_goal) }

let find_pattern_matches = find_matches (c1 true) Syntax.is_tpat

let find_sequent_matches bs ps s =
  let fm pat exp bs = find_pattern_matches bs (pat, exp) in
  fm ps.Calculus.frame s.Calculus.frame bs >>=
    fm ps.Calculus.hypothesis s.Calculus.hypothesis >>=
    fm ps.Calculus.conclusion s.Calculus.conclusion
(* }}} *)

let rec instantiate bs p =
  let on_var pv =
    match try_find pv bs with None -> pv | Some e -> e in
  let on_app po ps = Z3.FuncDecl.apply po (List.map (instantiate bs) ps) in
  (Syntax.on_var on_var & Syntax.on_app on_app) p

let instantiate_sequent bs s =
  { Calculus.frame = instantiate bs s.Calculus.frame
  ; hypothesis = instantiate bs s.Calculus.hypothesis
  ; conclusion = instantiate bs s.Calculus.conclusion }

let rules_of_calculus c =
  let apply_rule_schema rs s = (* RLP: Should we refer to some bindings here? *)
    let m = find_sequent_matches Syntax.ExprMap.empty rs.Calculus.goal_pattern s in
    List.map (fun bs -> List.map (instantiate_sequent bs) rs.Calculus.subgoal_pattern) m in
  let to_rule rs =
    { rule_name = rs.Calculus.schema_name
    ; rule_apply = apply_rule_schema rs } in
  id_rule
  :: or_rule
  :: smt_pure_rule
  :: or_rule
(*   :: abduce_instance_rule *)
  :: match_rule
  :: match_subformula_rule
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
  if log log_prove then fprintf logf "@{</details>@]";
  result

let solve_idfs min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@,@[<2>@{<details>@{<summary>start idfs proving@}@\n";
  let solve = flip (solve rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@{</details>@]@,@?";
  r

(* }}} *)
(* The top level interface. *) (* {{{ *)

let min_depth = 2
let max_depth = 3

let wrap_calculus f calculus =
  let rules = rules_of_calculus calculus in
  fun hypothesis conclusion ->
    f rules { Calculus.hypothesis; conclusion; frame = Syntax.mk_emp }

(* TODO: For efficiency, this shouldn't use matching rules (or anything that
looks like abduction). *)
let is_entailment rules goal =
  let penalty _ { Calculus.hypothesis; conclusion; _ } =
    if Syntax.expr_equal conclusion Syntax.mk_emp && Syntax.is_pure hypothesis
    then 0
    else Backtrack.max_penalty in
  let _, p = solve_idfs min_depth max_depth rules penalty goal in
  p = 0

let infer_frame rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    if is_instantiation conclusion
    then
      let _, hyp_spatial = extract_pure_part hypothesis in
      (n + 1) * (Syntax.size hyp_spatial)
    else Backtrack.max_penalty in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let biabduct rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    let _, hyp_spatial = extract_pure_part hypothesis in
    let _, con_spatial = extract_pure_part conclusion in
    (n + 1) * (Syntax.size hyp_spatial + Syntax.size con_spatial) in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []

let is_entailment = wrap_calculus is_entailment
let infer_frame = wrap_calculus infer_frame
let biabduct = wrap_calculus biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent rules e =
  is_entailment rules e (Z3.Boolean.mk_false z3_ctx)
(* }}} *)
