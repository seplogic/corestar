(* Modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

module Expr = Expression

(* }}} *)
type frame_and_antiframe =
  { frame : Expr.t
  ; antiframe : Expr.t }

(* Helper functions for prover rules. *) (* {{{ *)

let smt_hit, smt_miss = ref 0, ref 0
let smt_is_valid =
  let cache = Hashtbl.create 0 in
  fun a -> begin
    try
      let r = Hashtbl.find cache a in
      incr smt_hit;
      r
    with Not_found -> begin
      incr smt_miss;
      Smt.push ();
      Smt.say (Expr.mk_not a);
      let r = Smt.check_sat () = Smt.Unsat in
      Smt.pop ();
      Hashtbl.add cache a r;
      r
    end
  end

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
  Expr.cases (c1 [e]) (on (ListH.concatMap (unfold on)) & c2 [e]) e

(* Removes zero, and removes repetitions of pure parts.
Returns (pure, spatial) pair. *)
let ac_simplify_split is_zero on es =
  let xs = es >>= unfold on in
  let xs = List.filter (not @@ is_zero) xs in
  let xs, ys = List.partition Expr.is_pure xs in
  let module H = Hashtbl.Make (Expr) in
  let h = H.create (List.length xs) in
  List.iter (fun x -> H.replace h x ()) xs;
  (H.fold (fun x () xs -> x :: xs) h [], ys)

let ac_simplify is_zero on es =
  let xs, ys = ac_simplify_split is_zero on es in ys @ xs

let ac_make zero mk =
  function [] -> zero | [e] -> e | es -> mk es

(* Returns (pure, spatial) pair. *)
let extract_pure_part e =
  let mk = ac_make Expr.emp Expr.mk_big_star in
  let xs, ys = ac_simplify_split is_true Expr.on_star [e] in
  (mk xs, mk ys)

let mk_big_star =
  ac_make Expr.emp Expr.mk_big_star @@ ac_simplify is_true Expr.on_star

let mk_big_or =
  let is_false = Expr.equal Expr.fls in
  ac_make Expr.fls Expr.mk_big_or @@ ac_simplify is_false Expr.on_or

(* DBG
let mk_big_or e =
  printf "@[BEFORE %a@]@\n" (pp_list_sep "<||>" Expr.pp) e;
  let e = mk_big_or e in
  printf "@[AFTER %a@]@\n" Expr.pp e;
  e
*)

let mk_star e1 e2 = mk_big_star [e1; e2]
let mk_or e1 e2 = mk_big_or [e1; e2]

let mk_meet e1 e2 =
  let e1p, e1s = extract_pure_part e1 in
  let e2p, e2s = extract_pure_part e2 in
  if not (Expr.equal e1s Expr.emp && Expr.equal e2s Expr.emp)
  then Expr.fls (* TODO: More precise. *)
  else mk_star e1p e2p

let mk_big_meet = function
  | [] -> Expr.emp
  | e :: es -> List.fold_left mk_meet e es

(* TODO(rg): Add a comment with what this does. *)
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

(* Returns a list of expressions e' such that lvars(e*e') includes lvars(f).
More importantly, each e' is supposed to be a good guess of how to instantiate
the variables lvars(f)-lvars(e) such that e*e' ⊢ f. *)
let guess_instances e f =
  let get_lvars e =
    let vs = List.filter Expr.is_lvar (Expr.vars e) in
    List.fold_right StringSet.add vs StringSet.empty in
  let get_eq_args e =
    let module H = Hashtbl.Make (Expr) in
    let h = H.create 0 in
    let rec get e = Expr.match_ e
      undefined (* shouldn't be a variable *)
      ( Expr.on_star (List.iter get)
      & Expr.on_or (List.iter get)
      & Expr.on_eq (fun a _ -> H.replace h a ())
      & c2 () ) in
    get e;
    H.fold (fun x () xs -> x :: xs) h [] in
  let rec guess v f = (* finds g s.t. f contains v=g and g is not lvar *)
    let is_v = Expr.cases ((=) v) (c2 false) in
    let is_lvar = Expr.cases Expr.is_lvar (c2 false) in
    let do_eq a b =
      if is_v a && not (is_lvar b)
      then Some b
      else if is_v b && not (is_lvar a)
      then Some a
      else None in
    let rec do_star = function
      | [] -> None
      | e :: es -> (match guess v e with None -> do_star es | g -> g) in
    Expr.match_ f
      undefined ( Expr.on_star do_star & Expr.on_eq do_eq & c2 None ) in
  let collect_guess v (gs, ws) = match guess v f with
    | None -> (gs, v :: ws)
    | Some g -> ((v, g) :: gs, ws) in
  let vs = StringSet.diff (get_lvars f) (get_lvars e) in
  let vggs, vs = StringSet.fold collect_guess vs ([], []) in
  let bgs = get_eq_args e in
  let bgss = Misc.tuples (List.length vs) bgs in
  let vbgss = List.map (List.combine vs) bgss in
  let mk es =
    mk_big_star (List.map (fun (v, e) -> Expr.mk_eq (Expr.mk_var v) e) es) in
  List.map mk (List.map ((@) vggs) vbgss)

let smt_implies e f =
  Expr.is_pure e
  && Expr.is_pure f
  && smt_is_valid (Expr.mk_or (Expr.mk_not e) f)

let shuffle ls = ls (* XXX *)

let dbg_mc = ref 0
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
    prof_fun1 "Prover.id_rule"
    (function { Calculus.hypothesis; conclusion; _ } ->
      if Expr.equal hypothesis conclusion then [[]] else []) }

let or_rule =
  { rule_name = "or elimination"
  ; rule_apply =
    prof_fun1 "Prover.or_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let mk_goal c = [ { Calculus.hypothesis; conclusion = c; frame } ] in
      Expr.cases (c1 []) (Expr.on_or (List.map mk_goal) (c2 [])) conclusion) }

let smt_pure_rule =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    prof_fun1 "Prover.smt_pure_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (if not (Expr.equal conclusion Expr.emp) && smt_implies hypothesis conclusion 
      then [[{ Calculus.hypothesis; conclusion = Expr.emp; frame }]] else [])) }

(* ( H ⊢ C ) if ( H ⊢ I and H * I ⊢ C ) where
I is x1=e1 * ... * xn=en and x1,...,xn are lvars occuring in C but not H.
TODO: This rule is wrongly matching lvars from the spatial part of the
conclusion with terms from the pure part of the hypothesis. *)
let abduce_instance_rule =
  { rule_name = "guess value of lvar that occurs only on rhs"
  ; rule_apply =
    prof_fun1 "Prover.abduce_instance_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let _Is = guess_instances hypothesis conclusion in
      let mk _I =
        if Expr.equal _I Expr.emp || Expr.equal _I conclusion then None else
        Some
        [ { Calculus.hypothesis; conclusion = _I; frame = Expr.emp }
        ; { Calculus.hypothesis = mk_star hypothesis _I; conclusion; frame } ]
      in map_option mk _Is) }

(* TODO(rg): I don't understand why this rule isn't too specific. *)
let inline_pvars_rule =
  { rule_name = "substitution (of logical vars with program vars)"
  ; rule_apply =
    prof_fun1 "Prover.inline_pvars_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let subs = find_lvar_pvar_subs hypothesis in
      let sub_hyp = Expr.substitute subs hypothesis in
      let mk_eq (a, b) = Expr.mk_eq (Expr.mk_var a) b in
      let hyp = mk_big_star (sub_hyp :: List.map mk_eq subs) in
      if Expr.equal hyp hypothesis
      then []
      else [[{ Calculus.hypothesis = hyp; conclusion; frame}]]) }

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
let normalize = prof_fun1 "Prover.normalize" normalize

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

(* TODO: Maybe rename to expr_cases2, or even Expr.cases2? *)
let cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) =
  let on_pvar pv = Expr.cases (on_pvar_var pv) (on_pvar_op pv) e in
  let on_pop po ps = Expr.cases (on_pop_var po ps) (on_pop_op po ps) e in
  Expr.cases on_pvar on_pop p

(* Not needed as eq and neq are not comassoc
   They are not, as normalize_comassoc would not do the right thing on them
let on_pair f a b = f [a; b]
*)

let on_comassoc handle_comassoc handle_skew o es =
  ( Expr.on_star (handle_comassoc o)
  & Expr.on_or (handle_comassoc o)
(*
  & Expr.on_eq (on_pair handle_comassoc)
  & Expr.on_neq (on_pair handle_comassoc)
*)
  & handle_skew )
  o es

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
  printf "@[DBG find_matches@\np=(%a)@\ne=(%a)@]@\n" Expr.pp p Expr.pp e;
  let also_match = find_matches is_free can_be_op in
  let bind pv e =
    begin
      match try_find pv bs with
	| None -> [Done (StringMap.add pv e bs)]
	| Some oe -> if e = oe then [Done bs] else []
    end in
  let on_pvar_var pv ev =
    (* HACK: symmetric condition *probably* OK. *)
    if pv = ev then [Done bs]
    else if is_free pv then bind pv (Expr.mk_var ev)
    else if is_free ev then bind ev (Expr.mk_var pv)
    else [] in
  let on_pvar_op pv o es = if can_be_op pv then bind pv e else [] in
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

let expr_match_ops go e f =
  cases_pat_exp
    (fun v w -> invalid_arg ("expr_match_ops vv " ^ v ^ " and " ^ w))
    (fun v o _ -> invalid_arg ("expr_match_ops vo " ^ v ^ " and " ^ o))
    (fun o _ w -> invalid_arg ("expr_match_ops ov " ^ o ^ " and " ^ w))
    go
    (e, f)

let match_args = expr_match_ops
  (fun ep es fp fs ->
    if ep <> fp then None
    else let rec go eqs es fs = match es, fs with
      | [], [] -> Some (mk_big_star eqs)
      | [], _ | _, [] -> None
      | e :: es, f :: fs ->
          let eqs = if Expr.equal e f then eqs else Expr.mk_eq e f :: eqs in
          go eqs es fs in
      go [] es fs)

(* Notations:
    gs is an accumulator for subgoals found so far (any of them suffices)
    hp is the pure part of the hypothesis -- doesn't change
    cp is the pure part of the conclusion -- equalities are added to it
    fs is an accumulator for the frames matched so far
    nhs are the not matched parts of the hypothesis
    hs are the parts of the hypothesis not yet processed
    cs are the parts of the conclusion not yet processed *)
(* TODO: skip based on name, assuming sorting. *)
let rec list_spatial_matches gs hp cp fs nhs hs cs = match hs, cs with
  | [], ncs ->
      if fs <> []
      then (* found some frame *)
        { Calculus.frame = mk_big_star fs
        ; hypothesis = mk_big_star (hp :: nhs)
        ; conclusion = mk_big_star (cp :: ncs) }
        :: gs
      else gs
  | h :: hs, cs ->
      let rec try_c gs ds = function
        | [] -> list_spatial_matches gs hp cp fs (h :: nhs) hs cs
        | c :: cs ->
            let gs = (match match_args h c with
              | None -> gs
              | Some p ->
                  let cp = Expr.mk_star cp p in
                  if smt_is_valid (Expr.mk_not (Expr.mk_star hp cp))
                  then gs
                  else list_spatial_matches gs hp cp (h :: fs) nhs hs (ds @ cs)) in
            try_c gs (c :: ds) cs in
      try_c gs [] cs

(*
 m hypotheses
 n conclusions
 sum_k (n choose k) (m choose k) k!
*)

(* interpret free variables as existential variables *)
let find_existential_matches =
  find_matches Expr.is_lvar (c1 false)

let find_existential_sub_matches leftover_var bs (f, e) =
  printf "DBG (start find_existential_sub_matches@\n";
  let r = find_matches Expr.is_lvar ((=) leftover_var) bs (f, Expr.mk_star e Expr.emp) in
  printf "DBG find_existential_sub_matches stop)";
  r

(*
let find_existential_match = find_conversion Expr.is_lvar
*)

let spatial_id_rule =
  { rule_name = "spatial parts match"
  ; rule_apply =
    prof_fun1 "Prover.spatial_id_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      if log log_prove then fprintf logf "hp: %a@ hs: %a@ cp: %a@ cs: %a"
	Expr.pp hyp_pure Expr.pp hyp_spatial Expr.pp conc_pure Expr.pp conc_spatial;
      if Expr.equal hyp_spatial Expr.emp && Expr.equal conc_spatial Expr.emp
        then []
      else if Expr.equal hyp_spatial conc_spatial (* should really be handled by matching *)
        then [[{ Calculus.hypothesis = hyp_pure; conclusion = conc_pure; frame}]]
      else begin
        let matches = find_existential_matches StringMap.empty (conc_spatial, hyp_spatial) in
        if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
        let mk_goal m =
          let b = StringMap.bindings m in
          let mk_eq (v, e) = Expr.mk_eq (Expr.mk_var v) e in
          [ { Calculus.hypothesis = hyp_pure
            ; conclusion = mk_big_star (conc_pure :: List.map mk_eq b)
            ; frame } ] in
        List.map mk_goal matches
      end) }

let match_rule =
  { rule_name = "matching free variables"
  ; rule_apply =
    prof_fun1 "Prover.match_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let matches =
	  find_existential_matches StringMap.empty (conclusion, hypothesis) in
      if log log_prove then fprintf logf "@,found %d matches@\n" (List.length matches);
      let mk_goal m =
	let b = StringMap.bindings m in
	let mk_eq (v, e) = Expr.mk_eq (Expr.mk_var v) e in
	[ { Calculus.hypothesis = hypothesis
	  ; conclusion = mk_big_star (List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

let match_subformula_rule =
  { rule_name = "matching spatial subformula"
  ; rule_apply =
    prof_fun1 "Prover.match_subformula_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      if Expr.equal Expr.emp conc_spatial
      then [] else begin
        let lo_name = "_leftover" in assert (Expr.is_lvar lo_name);
        let leftover = Expr.mk_var lo_name in
        let enhanced_conc = Expr.mk_star leftover conc_spatial in
        let matches =
          find_existential_sub_matches lo_name StringMap.empty (enhanced_conc, hyp_spatial) in
        if log log_prove then
          fprintf logf "@,trying to match %a and % a@,"
            Expr.pp enhanced_conc Expr.pp hyp_spatial;
        if log log_prove then
          fprintf logf "@,@[<v 2>found %d matches:@,%a@,@]"
            (List.length matches)
            (pp_list_sep "\n" (fun f m -> fprintf f "[ %a ]" (pp_list_sep "; " (fun f (v,e) -> fprintf f "%s->%a" v Expr.pp e)) (StringMap.bindings m))) matches;
        let mk_goal m =
          let leftover_match = StringMap.find lo_name m in
          [ [ { Calculus.hypothesis = mk_star leftover_match hyp_pure
              ; conclusion = conc_pure
              ; frame = mk_star frame conc_spatial } ] ] in
        matches >>= mk_goal
      end) }

(* This is intended as a lightweight version of [match_subformula_rule]. *)
let spatial_match_rule =
  { rule_name = "spatial match (lightweight)"
  ; rule_apply =
    prof_fun1 "Prover.spatial_match_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (* TODO: don't apply rule if hyp & conc have disjunctions. *)
      let hyp_pure, hs = ac_simplify_split is_true Expr.on_star [hypothesis] in
      let conc_pure, cs = ac_simplify_split is_true Expr.on_star [conclusion] in
      let hyp_pure = mk_big_star hyp_pure in
      let conc_pure = mk_big_star conc_pure in
(* TODO: Activate this once list_spatial_matches takes advantage of sorting.
      let cmp =
        (expr_match_ops
          (fun o1 es1 o2 es2 ->
            let oc = compare o1 o2 in
            if oc <> 0
            then oc
            else compare (List.length es1) (List.length es2))) in
      let hs = List.sort cmp hs in
      let cs = List.sort cmp cs in *)
      let gs = list_spatial_matches [] hyp_pure conc_pure [] [] hs cs in
      List.map (fun x -> [x]) gs) }

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

let builtin_rules =
  [ id_rule
(*   ; spatial_match_rule (* should be before abduce_instance_rule *) *)
  ; abduce_instance_rule
(*   ; spatial_id_rule *)
  ; smt_pure_rule
(*   ; or_rule *)
  ; match_rule (* XXX: subsumed by match_subformula_rule? *)
(*   ; match_subformula_rule *)
  ; inline_pvars_rule ]

(* These are used for [is_entailment], which wouldn't benefit from instantiating
lvars. *)
let builtin_rules_noinst =
  [ id_rule
  ; smt_pure_rule
  ; inline_pvars_rule
  ; spatial_id_rule ]


let rules_of_calculus builtin c =
  let apply_rule_schema rs s = (* RLP: Should we refer to some bindings here? *)
    let m = find_sequent_matches StringMap.empty rs.Calculus.goal_pattern s in
    List.map (fun bs -> List.map (instantiate_sequent bs) rs.Calculus.subgoal_pattern) m in
  let to_rule rs =
    { rule_name = rs.Calculus.schema_name
    ; rule_apply = prof_fun1 "user_rule" (apply_rule_schema rs) } in
  builtin @ List.map to_rule c


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
  if log log_prove then fprintf logf "@{<summary>goal@@%d:@} @{<p>%a@}@," n CalculusOps.pp_sequent goal;
  let leaf = ([goal], penalty n goal) in
  if log log_prove then fprintf logf "@{<p>Current goal has penalty %d at level %d@}@\n" (penalty n goal) n;
  let result =
    if n = 0 then leaf else begin
      let process_rule r =
        if log log_prove then fprintf logf "@{<p>apply rule %s@}@\n" r.rule_name;
        let ess = r.rule_apply goal in
        if safe then assert (List.for_all (List.for_all (not @@ (=) goal)) ess);
        ess in
      let solve_subgoal = solve rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  if log log_prove then fprintf logf "@}@]@\n";
  result

let solve_idfs min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@[<2>@{<details>@{<summary>start idfs proving@}@\n";
  let solve = flip (solve rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@}@]@\n@?";
  r

(* }}} *)
(* Penalty functions. *) (* {{{ *)

let rec heap_size e = Expr.match_ e
  undefined
  ( Expr.on_emp (c1 0)
  & Expr.on_eq (c2 0)
  & Expr.on_fls (c1 0)
  & Expr.on_neq (c2 0)
  & Expr.on_not heap_size
  & Expr.on_or (List.fold_left max 0 @@ List.map heap_size)
  & Expr.on_star (List.fold_left (+) 0 @@ List.map heap_size)
  & Expr.on_string_const undefined
  & Expr.on_int_const undefined
  & fun op _ -> if Expr.is_pure_op op then 0 else 1)

(* }}} *)
(* The top level interface. *) (* {{{ *)

let min_depth = 2
let max_depth = 6

let wrap_calculus builtin f calculus =
  let rules = rules_of_calculus builtin calculus in
  fun hypothesis conclusion ->
    f rules { Calculus.hypothesis; conclusion; frame = Expr.emp }

let is_entailment rules goal =
  let penalty _ { Calculus.hypothesis; conclusion; _ } =
    if Expr.equal conclusion Expr.emp && Expr.is_pure hypothesis
    then 0
    else Backtrack.max_penalty in
  let _, p = solve_idfs min_depth max_depth rules penalty goal in
  p = 0
let is_entailment = prof_fun2 "Prover.is_entailment" is_entailment

let infer_frame rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    if is_instantiation conclusion
    then (n + 1) * heap_size hypothesis
    else Backtrack.max_penalty in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []
let infer_frame = prof_fun2 "Prover.infer_frame" infer_frame

let biabduct rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    (n + 1) * (heap_size hypothesis + heap_size conclusion) in
  let ss, p = solve_idfs min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []
let biabduct = prof_fun2 "Prover.biabduct" biabduct

let is_entailment = wrap_calculus builtin_rules_noinst is_entailment
let infer_frame = wrap_calculus builtin_rules infer_frame
let biabduct = wrap_calculus builtin_rules biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent rules e =
  is_entailment rules e Expr.fls
let is_inconsistent = prof_fun2 "Prover.is_inconsistent" is_inconsistent


let pp_stats () =
  fprintf logf "smt_hit %d@\n" !smt_hit;
  fprintf logf "smt_miss %d@\n" !smt_miss
(* }}} *)
