(* Modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

(* }}} *)

type frame_and_antiframe =
  { frame : Z3.Expr.expr
  ; antiframe : Z3.Expr.expr }

(* Helper functions for prover rules. *) (* {{{ *)

let smt_hit, smt_miss = ref 0, ref 0
let smt_is_valid ctx =
  let cache = Syntax.ExprHashMap.create 0 in
  fun a -> begin
    try
      let r = Syntax.ExprHashMap.find cache a in
      incr smt_hit;
      r
    with Not_found -> begin
      incr smt_miss;
      Smt.push ctx;
      Smt.say ctx (Z3.Boolean.mk_not (Syntax.z3_context ctx) a);
      let r = Smt.check_sat ctx = Smt.Unsat in
      Smt.pop ctx;
      Syntax.ExprHashMap.add cache a r;
      r
    end
  end

(* True iff _x1=e1 * _x2=e2 * ... *)
let rec is_instantiation ctx e =
(*   printf "oops@\n@?"; *)
  let chk_eq f1 f2 = Syntax.is_lvar f1 || Syntax.is_lvar f2 in
  let chk_distinct f = List.exists Syntax.is_lvar f in
  (Syntax.on_emp ctx (c1 true)
   & Syntax.on_star ctx (fun a b -> is_instantiation ctx a && is_instantiation ctx b)
   & Syntax.on_eq chk_eq
   & Syntax.on_distinct chk_distinct
   & c1 false) e

let is_emp ctx e =
  (Syntax.on_emp ctx (c1 true)
   & Syntax.on_eq Syntax.expr_equal
   & c1 false) e

let rec unfold on e =
  (Syntax.on_var (c1 [e])
   & (on (ListH.concatMap (unfold on)) & c1 [e]))
    e

(* Removes zero, and removes repetitions of pure parts.
Returns (pure, spatial) pair. *)
let ac_simplify_split ctx is_zero on es =
  let xs = es >>= unfold (on ctx) in
  let xs = List.filter (not @@ is_zero ctx) xs in
  let xs, ys = List.partition (Syntax.is_pure ctx) xs in
  let h = Syntax.ExprHashSet.create (List.length xs) in
  List.iter (fun x -> Syntax.ExprHashSet.add h x) xs;
  (Syntax.ExprHashSet.fold (fun x xs -> x :: xs) h [], ys)

let ac_simplify ctx is_zero on es =
  let xs, ys = ac_simplify_split ctx is_zero on es in ys @ xs

let ac_make ctx zero mk =
  function [] -> zero ctx | [e] -> e | es -> mk ctx es

(* Returns (pure, spatial) pair. *)
let extract_pure_part ctx e =
  let mk = ac_make ctx Syntax.mk_emp Syntax.mk_big_star in
  let xs, ys = ac_simplify_split ctx is_emp Syntax.on_big_star [e] in
  (mk xs, mk ys)

let mk_big_star ctx l =
  (ac_make ctx Syntax.mk_emp Syntax.mk_big_star @@ ac_simplify ctx is_emp Syntax.on_big_star) l

let mk_big_or ctx =
  ac_make ctx Syntax.mk_false Syntax.mk_big_or @@
    ac_simplify ctx (fun _ -> Z3.Expr.is_false) (fun _ -> Syntax.on_or)

(* DBG
let mk_big_or e =
  printf "@[BEFORE %a@]@\n" (pp_list_sep "<||>" Expr.pp) e;
  let e = mk_big_or e in
  printf "@[AFTER %a@]@\n" Expr.pp e;
  e
*)

let mk_star ctx e1 e2 = mk_big_star ctx [e1; e2]
let mk_or ctx e1 e2 = mk_big_or ctx [e1; e2]

let mk_meet ctx e1 e2 =
  let e1p, e1s = extract_pure_part ctx e1 in
  let e2p, e2s = extract_pure_part ctx e2 in
  let emp = Syntax.mk_emp ctx in
  if not (Syntax.expr_equal e1s emp && Syntax.expr_equal e2s emp)
  then (Syntax.mk_false ctx) (* TODO: More precise. *)
  else mk_star ctx e1p e2p

let mk_big_meet ctx = function
  | [] -> Syntax.mk_emp ctx
  | [e] -> e
  | e :: es -> List.fold_left (mk_meet ctx) e es

(* TODO(rg): Add a comment with what this does. *)
let find_lvar_pvar_subs ctx e =
  let add_if_good l =
    Syntax.on_eq
      (fun a b ->
	if Syntax.is_lvar a && Syntax.is_pvar b then (a, b)::l
	else if Syntax.is_pvar a && Syntax.is_lvar b then (b, a)::l
	else l)
    & (c1 l) in
  let get_subs = List.fold_left add_if_good [] in
  (Syntax.on_big_star ctx get_subs (fun _ -> [])) e

(* Handles ss=[],
and caries over the pure parts of the antiframe into the frame. *)
let afs_of_sequents ctx = function
  | [] -> [{ frame = Syntax.mk_emp ctx; antiframe = Syntax.mk_emp ctx }]
  | ss ->
      let f { Calculus.hypothesis; conclusion; _ } =
        let frame = hypothesis in
        let antiframe = conclusion in
        let pa, _ = extract_pure_part ctx antiframe in
        let frame = mk_star ctx frame pa in
        { frame; antiframe } in
      List.map f ss

(* Returns a list of expressions e' such that lvars(e*e') includes lvars(f).
More importantly, each e' is supposed to be a good guess of how to instantiate
the variables lvars(f)-lvars(e) such that e*e' ⊢ f. *)
let guess_instances ctx e f =
  let module VS = Syntax.ExprSet in
  let get_lvars e =
    let vs = List.filter Syntax.is_lvar (Syntax.vars e) in
    List.fold_right VS.add vs VS.empty in
  let get_eq_args e =
    let module H = Syntax.ExprHashSet in
    let h = H.create 0 in
    let h_eq = H.create 0 in (* ∀x in h_eq, there is y in h s.t. x=y *)
    let add a b =
      if not (H.mem h_eq a || H.mem h_eq b) then H.add h a;
      H.add h_eq a; H.add h_eq b in
    let rec get e =
      ( Syntax.on_big_star ctx (List.iter get)
      & Syntax.on_or (List.iter get)
      & Syntax.on_eq add
      & Syntax.on_distinct (List.iter (fun x -> add x x))
      & Syntax.on_app (c2 ())) e in
    get e;
    H.fold ListH.cons h [] in
  let rec guess v f = (* finds g s.t. f contains v=g and g is not lvar *)
    let is_v = Syntax.on_var (Syntax.expr_equal v) & Syntax.on_app (c2 false) in
    let do_eq a b =
      if is_v a && not (Syntax.is_lvar b)
      then Some b
      else if is_v b && not (Syntax.is_lvar a)
      then Some a
      else None in
    let rec do_star = function
      | [] -> None
      | e :: es -> (match guess v e with None -> do_star es | g -> g) in
    ( Syntax.on_big_star ctx do_star
    & Syntax.on_eq do_eq
    & Syntax.on_app (c2 None)) f in
  let collect_guess v (gs, ws) = match guess v f with
    | None -> (gs, v :: ws)
    | Some g -> ((v, g) :: gs, ws) in
  let vs = VS.diff (get_lvars f) (get_lvars e) in
  let vggs, vs = VS.fold collect_guess vs ([], []) in
  let bgs = get_eq_args e in
  let bgss = Misc.tuples (List.length vs) bgs in
  let vbgss = List.map (List.combine vs) bgss in
  let mk es = mk_big_star ctx (List.map (fun (v, e) -> Syntax.mk_eq ctx v e) es) in
  List.map mk (List.map ((@) vggs) vbgss)

let smt_implies ctx e f =
  Syntax.is_pure ctx e
  && Syntax.is_pure ctx f
  && smt_is_valid ctx (Syntax.mk_or ctx (Syntax.mk_not ctx e) f)

let shuffle ls = ls (* XXX *)

let dbg_mc = ref 0
(* }}} *)
(* Prover rules, including those provided by the user. *) (* {{{ *)
type named_rule =
  { rule_name : string (* For debug *)
  (** If ([rule_apply] [x]) is [[a;b];[c]], then a and b together are sufficient
  to prove [x], and so is c alone. *)
  ; rule_apply : Calculus.sequent -> Calculus.sequent list list }

let id_rule =
  { rule_name = "identity axiom"
  ; rule_apply =
    prof_fun1 "Prover.id_rule"
    (function { Calculus.hypothesis; conclusion; _ } ->
      if Syntax.expr_equal hypothesis conclusion then [[]] else []) }

let or_rule =
  { rule_name = "or elimination"
  ; rule_apply =
    prof_fun1 "Prover.or_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let mk_goal c = [ { Calculus.hypothesis; conclusion = c; frame } ] in
      (Syntax.on_or (List.map mk_goal) & (c1 [])) conclusion) }

let smt_pure_rule ctx =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    prof_fun1 "Prover.smt_pure_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (if not (Syntax.expr_equal conclusion (Syntax.mk_emp ctx)) && smt_implies ctx hypothesis conclusion 
      then [[{ Calculus.hypothesis; conclusion = Syntax.mk_emp ctx; frame }]] else [])) }

(* ( H ⊢ C ) if ( H ⊢ I and H * I ⊢ C ) where
I is x1=e1 * ... * xn=en and x1,...,xn are lvars occuring in C but not H.
TODO: This rule is wrongly matching lvars from the spatial part of the
conclusion with terms from the pure part of the hypothesis. *)
let abduce_instance_rule ctx =
  { rule_name = "guess value of lvar that occurs only on rhs"
  ; rule_apply =
    prof_fun1 "Prover.abduce_instance_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let is_or =
        ( Syntax.on_var (c1 false)
        & Syntax.on_or (c1 true)
        & Syntax.on_app (c2 false)) in
      if is_or conclusion then [] else begin
        let _Is = guess_instances ctx hypothesis conclusion in
        let mk _I =
          if Syntax.expr_equal _I (Syntax.mk_emp ctx) || Syntax.expr_equal _I conclusion
          then None
          else Some
          [ { Calculus.hypothesis; conclusion = _I; frame = Syntax.mk_emp ctx }
          ; { Calculus.hypothesis = mk_star ctx hypothesis _I; conclusion; frame } ]
        in map_option mk _Is
      end) }

(* returns [true] if [v] appears at least twice in [e] *)
let appears_twice e v =
  let rec check f =
    let is_v =
      let n = ref 0 in
      fun ff ->
	if Syntax.expr_equal v ff then incr n;
	!n >= 2 in
    is_v f || Syntax.on_app (fun _ xs -> List.exists check xs) f in
  check e

(* TODO(rg): I don't understand why this rule isn't too specific. *)
let inline_pvars_rule ctx =
  { rule_name = "substitution (of logical vars with program vars)"
  ; rule_apply =
    prof_fun1 "Prover.inline_pvars_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let subs = find_lvar_pvar_subs ctx hypothesis in
      let subs = List.filter (appears_twice hypothesis @@ fst) subs in
      let (subees, subers) = List.split subs in
      if subees = [] then []
      else
	let sub_hyp = Z3.Expr.substitute hypothesis subees subers in
	let mk_eq (a, b) = Syntax.mk_eq ctx a b in
	let hyp = mk_big_star ctx (sub_hyp :: List.map mk_eq subs) in
	if Syntax.expr_equal hyp hypothesis
	then []
	else [[{ Calculus.hypothesis = hyp; conclusion; frame}]]) }

(* A root-leaf path of the result matches ("or"?; "star"?; "not"?; OTHER).
The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
and "not". *)
let normalize ctx =
  let rec not_not e =
    let e = (Syntax.on_var (c1 e)
             & Syntax.on_app (Syntax.recurse not_not)) e in
    let negate e =
      let ne = Z3.Boolean.mk_not (Syntax.z3_context ctx) e in
      (Syntax.on_not c0 & c1 ne) e in
    (Syntax.on_not negate & c1 e) e in
  let rec star_below_or e = (* (a∨b)*(c∨d) becomes (a*c)∨(a*d)∨(b*c)∨(b*d) *)
    let ess = List.map (unfold Syntax.on_or) (unfold (Syntax.on_big_star ctx) e) in
    let fss = Misc.product ess in
    let r f = if Syntax.expr_equal f e then f else star_below_or f in
    let fs = List.map (r @@ mk_big_star ctx) fss in
    mk_big_or ctx fs in
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
    ; forbid_not (Syntax.on_star ctx) ] in
  List.fold_left (@@) id fs
let normalize = prof_fun1 "Prover.normalize" normalize

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

(* TODO: Maybe rename to expr_cases2, or even Expr.cases2? *)
let cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) =
  let on_pvar pv = (Syntax.on_var (on_pvar_var pv) & Syntax.on_app (on_pvar_op pv)) e in
  let on_pop po ps = (Syntax.on_var (on_pop_var po ps) & Syntax.on_app (on_pop_op po ps)) e in
  (Syntax.on_var on_pvar & Syntax.on_app on_pop) p

(* Not needed as eq and neq are not comassoc
   They are not, as normalize_comassoc would not do the right thing on them
let on_pair f a b = f [a; b]
*)

let on_comassoc ctx handle_comassoc handle_skew e =
  ( Syntax.on_big_star ctx handle_comassoc
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
let normalize_comassoc ctx e =
  let unfold = function [x] -> x | _ -> e in
  (on_comassoc ctx unfold (c1 e)) e

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

let rec find_matches ctx is_free can_be_op bs (p, e) =
  let also_match = find_matches ctx is_free can_be_op in
  let bind pv =
    begin
      match try_find pv bs with
	| None -> [Done (Syntax.ExprMap.add pv e bs)]
	| Some oe -> if Syntax.expr_equal e oe then [Done bs] else []
    end in
  (* TODO: We might need a symmetric condition. *)
  let on_pvar_var pv ev = if is_free pv then bind pv else if Syntax.expr_equal pv ev then [Done bs] else [] in
  let on_pvar_op pv o es = if can_be_op pv then bind pv else [] in
  let on_pop_var _ _ _ = [] in
  let on_pop_op po ps o es =
    if not (Z3.FuncDecl.equal po o) then []
    else
      let handle_comassoc _ =
	begin
	  let mk_o l =
	    (* this is a HACK to avoid creating invalid Z3
	       expressions: '*' is a binary operation as far as Z3 is
	       concerned, so it can only be applied to arbitrary lists
	       of elements via mk_big_star *)
	    if Z3.FuncDecl.equal o (Syntax.star ctx) then mk_big_star ctx l
	    else Z3.FuncDecl.apply o l in
	  match ps with
	  | [] -> if es = [] then [Done bs] else []
	  | [x] -> List.map (fun m -> Done m) (also_match bs (x, normalize_comassoc ctx e))
	  | ext_p::rest_p ->
	    begin
	      let unspecific v =
		let is_more (yes, no) =
		  let to_bind = normalize_comassoc ctx (mk_o yes) in
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
      on_comassoc ctx handle_comassoc handle_skew (Z3.FuncDecl.apply po ps) in
  let matches = cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) in
  let process_match = function
    | Done final_bs -> [final_bs]
    | More (next_bs, next_pair) -> also_match next_bs next_pair in
  matches >>= process_match

let expr_match_ops go e f =
  let err _ =
    fprintf str_formatter
      "expr_match_ops %a and %a" Syntax.pp_expr e Syntax.pp_expr f;
    invalid_arg (flush_str_formatter ()) in
  cases_pat_exp
    (c1 err) (c2 err) (c2 err)
    go
    (e, f)

let match_args ctx = expr_match_ops
  (fun ep es fp fs ->
    if ep <> fp then None
    else let rec go eqs es fs = match es, fs with
      | [], [] -> Some (mk_big_star ctx eqs)
      | [], _ | _, [] -> None
      | e :: es, f :: fs ->
          let eqs = if Syntax.expr_equal e f then eqs else Syntax.mk_eq ctx e f :: eqs in
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
let rec list_spatial_matches ctx gs hp cp fs nhs hs cs = match hs, cs with
  | [], ncs ->
      if fs <> []
      then (* found some frame *)
        { Calculus.frame = mk_big_star ctx fs
        ; hypothesis = mk_big_star ctx (hp :: nhs)
        ; conclusion = mk_big_star ctx (cp :: ncs) }
        :: gs
      else gs
  | h :: hs, cs ->
      let rec try_c gs ds = function
        | [] -> list_spatial_matches ctx gs hp cp fs (h :: nhs) hs cs
        | c :: cs ->
            let gs = (match match_args ctx h c with
              | None -> gs
              | Some p ->
                  let cp = Syntax.mk_star ctx cp p in
                  if smt_is_valid ctx (Syntax.mk_not ctx (Syntax.mk_star ctx hp cp))
                  then gs
                  else list_spatial_matches ctx gs hp cp (h :: fs) nhs hs (ds @ cs)) in
            try_c gs (c :: ds) cs in
      try_c gs [] cs

(*
 m hypotheses
 n conclusions
 sum_k (n choose k) (m choose k) k!
*)
(*
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
let find_existential_matches ctx =
  find_matches ctx Syntax.is_lvar (c1 false)

let find_existential_sub_matches ctx leftover_var =
  find_matches ctx Syntax.is_lvar (Syntax.expr_equal leftover_var)

(*
let find_existential_match = find_conversion Syntax.is_lvar
*)

let spatial_id_rule ctx =
  { rule_name = "spatial parts match"
  ; rule_apply =
    prof_fun1 "Prover.spatial_id_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part ctx hypothesis in
      let conc_pure, conc_spatial = extract_pure_part ctx conclusion in
      if log log_prove then fprintf logf "hp: %a@ hs: %a@ cp: %a@ cs: %a"
	Syntax.pp_expr hyp_pure Syntax.pp_expr hyp_spatial Syntax.pp_expr conc_pure Syntax.pp_expr conc_spatial;
      if Syntax.expr_equal hyp_spatial (Syntax.mk_emp ctx)
	&& Syntax.expr_equal conc_spatial (Syntax.mk_emp ctx)
      then []
      else if Syntax.expr_equal hyp_spatial conc_spatial (* should really be handled by matching *)
        then [[{ Calculus.hypothesis = hyp_pure; conclusion = conc_pure; frame}]]
      else begin
        let matches = find_existential_matches ctx Syntax.ExprMap.empty (conc_spatial, hyp_spatial) in
        if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
        let mk_goal m =
          let b = Syntax.ExprMap.bindings m in
          let mk_eq (v, e) = Syntax.mk_eq ctx v e in
          [ { Calculus.hypothesis = hyp_pure
            ; conclusion = mk_big_star ctx (conc_pure :: List.map mk_eq b)
            ; frame } ] in
        List.map mk_goal matches
      end) }

let match_rule ctx =
  { rule_name = "matching free variables"
  ; rule_apply =
    prof_fun1 "Prover.match_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let matches =
	  find_existential_matches ctx Syntax.ExprMap.empty (conclusion, hypothesis) in
      if log log_prove then fprintf logf "@,found %d matches@\n" (List.length matches);
      let mk_goal m =
	let b = Syntax.ExprMap.bindings m in
	let mk_eq (v, e) = Syntax.mk_eq ctx v e in
	[ { Calculus.hypothesis = hypothesis
	  ; conclusion = mk_big_star ctx (List.map mk_eq b)
	  ; frame } ] in
      List.map mk_goal matches) }

let match_subformula_rule ctx =
  { rule_name = "matching spatial subformula"
  ; rule_apply =
    prof_fun1 "Prover.match_subformula_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part ctx hypothesis in
      let conc_pure, conc_spatial = extract_pure_part ctx conclusion in
      if Syntax.expr_equal (Syntax.mk_emp ctx) conc_spatial
      then [] else begin
        let lo_name = "_leftover" in
        let leftover = Syntax.mk_lvar ctx lo_name in
        let enhanced_conc = Syntax.mk_star ctx leftover conc_spatial in
        let matches =
          find_existential_sub_matches ctx leftover Syntax.ExprMap.empty (enhanced_conc, hyp_spatial) in
        if log log_prove then
          fprintf logf "@,trying to match %a and % a@,"
            Syntax.pp_expr enhanced_conc Syntax.pp_expr hyp_spatial;
        if log log_prove then begin
          fprintf logf "@,@[<v 2>found %d matches:@,%a@,@]"
            (List.length matches)
            (pp_list_sep "\n"
              (fun f m -> fprintf f "[ %a ]"
                (pp_list_sep "; "
                  (fun f (v,e) -> fprintf f "%a->%a" Syntax.pp_expr v Syntax.pp_expr e))
                (Syntax.ExprMap.bindings m)))
            matches end;
        let mk_goal m =
          let leftover_match = Syntax.ExprMap.find leftover m in
          [ [ { Calculus.hypothesis = mk_star ctx leftover_match hyp_pure
              ; conclusion = conc_pure
              ; frame = mk_star ctx frame conc_spatial } ] ] in
        matches >>= mk_goal
      end) }

(* This is intended as a lightweight version of [match_subformula_rule]. *)
let spatial_match_rule ctx =
  { rule_name = "spatial match (lightweight)"
  ; rule_apply =
    prof_fun1 "Prover.spatial_match_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (* TODO: don't apply rule if hyp & conc have disjunctions. *)
      let hyp_pure, hs = ac_simplify_split ctx is_emp Syntax.on_big_star [hypothesis] in
      let conc_pure, cs = ac_simplify_split ctx is_emp Syntax.on_big_star [conclusion] in
      let hyp_pure = mk_big_star ctx hyp_pure in
      let conc_pure = mk_big_star ctx conc_pure in
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
      let gs = list_spatial_matches ctx [] hyp_pure conc_pure [] [] hs cs in
      List.map (fun x -> [x]) gs) }

let find_pattern_matches ctx = find_matches ctx (c1 true) Syntax.is_tpat

let find_sequent_matches ctx bs ps s =
  let fm pat exp bs = find_pattern_matches ctx bs (pat, exp) in
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

let builtin_rules ctx =
  [ id_rule
(*   ; spatial_match_rule (* should be before abduce_instance_rule *) *)
  ; abduce_instance_rule ctx
(*   ; spatial_id_rule *)
  ; smt_pure_rule ctx
(*   ; or_rule *)
(*   ; match_rule (* XXX: subsumed by match_subformula_rule? *) *)
(*   ; match_subformula_rule *)
  ; inline_pvars_rule ctx ]

(* These are used for [is_entailment], which wouldn't benefit from instantiating
lvars. *)
let builtin_rules_noinst ctx =
  [ id_rule
  ; smt_pure_rule ctx
  ; inline_pvars_rule ctx
  ; spatial_id_rule ctx ]


let rules_of_calculus ctx builtin c =
  let apply_rule_schema rs s = (* RLP: Should we refer to some bindings here? *)
    let m = find_sequent_matches ctx Syntax.ExprMap.empty rs.Calculus.goal_pattern s in
    let side_cond = Syntax.mk_big_or ctx (List.map (flip instantiate rs.Calculus.side_condition) m) in
    if smt_is_valid ctx side_cond then
      List.map (fun bs -> List.map (instantiate_sequent bs) rs.Calculus.subgoal_pattern) m
    else [] in
  let to_rule rs =
    { rule_name = rs.Calculus.schema_name
    ; rule_apply = prof_fun1 "user_rule" (apply_rule_schema rs) } in
  builtin ctx @ List.map to_rule c


(* }}} *)
(* The main proof-search algorithm. *) (* {{{ *)

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with
with score [> Backtrack.max_penalty] needs a proof.  Anything in-between is kind
of acceptable as a leaf, but we should keep looking for something better.
  TODO: we may want min_penalty and max_penalty decrease with the level n
  TODO: we may want to count only once a leaf appearing twice
  TODO: we may want to partly cache the results of proving
*)
let rec solve ctx rules penalty n { Calculus.frame; hypothesis; conclusion } =
  if log log_prove then fprintf logf "@[<2>@{<details>";
  let goal =
    { Calculus.frame = normalize ctx frame
    ; hypothesis = normalize ctx hypothesis
    ; conclusion = normalize ctx conclusion } in
  if log log_prove then fprintf logf "@{<summary>goal@@%d:@} @{<p>%a@}@," n CalculusOps.pp_sequent goal;
  let leaf = ([goal], penalty n goal) in
  if log log_prove then fprintf logf "@{<p>Current goal has penalty %d at level %d@}@\n" (penalty n goal) n;
  let result =
    if n = 0 then leaf else begin
      let process_rule r =
	if log log_prove then fprintf logf "@{<p>apply rule %s@}@\n" r.rule_name;
        let ess = r.rule_apply goal in
        if safe then assert (List.for_all (List.for_all (not @@ Calculus.sequent_equal goal)) ess);
        ess in
      let solve_subgoal = solve ctx rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  if log log_prove then fprintf logf "@}@]@\n";
  result

let solve_idfs ctx min_depth max_depth rules penalty goal =
  if log log_prove then fprintf logf "@[<2>@{<details>@{<summary>start idfs proving@}@\n";
  let solve = flip (solve ctx rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@}@]@\n@?";
  r

(* }}} *)
(* Penalty functions. *) (* {{{ *)

let rec heap_size ctx e =
  if Syntax.is_pure ctx e then 0 else
  ( Syntax.on_not (heap_size ctx)
  & Syntax.on_or (List.fold_left max 0 @@ List.map (heap_size ctx))
  & Syntax.on_big_star ctx (List.fold_left (+) 0 @@ List.map (heap_size ctx))
  & c1 1) e

(* }}} *)
(* The top level interface. *) (* {{{ *)

let min_depth = 2
let max_depth = 6

let wrap_calculus ctx builtin f calculus =
  let rules = rules_of_calculus ctx builtin calculus in
  fun hypothesis conclusion ->
    f ctx rules { Calculus.hypothesis; conclusion; frame = Syntax.mk_emp ctx }

let is_entailment ctx rules goal =
  let penalty _ { Calculus.hypothesis; conclusion; _ } =
    if Syntax.expr_equal conclusion (Syntax.mk_emp ctx) && Syntax.is_pure ctx hypothesis
    then 0
    else Backtrack.max_penalty in
  let _, p = solve_idfs ctx min_depth max_depth rules penalty goal in
  p = 0
let is_entailment = prof_fun2 "Prover.is_entailment" is_entailment

let infer_frame ctx rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    if is_instantiation ctx conclusion
    then (n + 1) * heap_size ctx hypothesis
    else Backtrack.max_penalty in
  let ss, p = solve_idfs ctx min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ctx ss else []
let infer_frame = prof_fun2 "Prover.infer_frame" infer_frame

let biabduct ctx rules goal =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    (n + 1) * (heap_size ctx hypothesis + heap_size ctx conclusion) in
  let ss, p = solve_idfs ctx min_depth max_depth rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ctx ss else []
let biabduct = prof_fun2 "Prover.biabduct" biabduct

let is_entailment ctx = wrap_calculus ctx builtin_rules_noinst is_entailment
let infer_frame ctx = wrap_calculus ctx builtin_rules infer_frame
let biabduct ctx = wrap_calculus ctx builtin_rules biabduct
(* NOTE: [simplify] is defined in the beginning. *)

let is_inconsistent ctx rules e =
  is_entailment ctx rules e (Syntax.mk_false ctx)
let is_inconsistent = prof_fun2 "Prover.is_inconsistent" is_inconsistent


let print_stats () =
  fprintf logf "smt_hit %d@\n" !smt_hit;
  fprintf logf "smt_miss %d@\n" !smt_miss
(* }}} *)
