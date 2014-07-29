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
  let has_lvar = List.exists Syntax.is_lvar in
  (Syntax.on_emp (c1 true)
   & Syntax.on_star (fun a b -> is_instantiation a && is_instantiation b)
   & Syntax.on_eq (fun a b -> has_lvar [a; b])
   & Syntax.on_distinct has_lvar
   & c1 false) e

let is_emp e =
  (Syntax.on_emp (c1 true)
   & Syntax.on_eq Syntax.expr_equal
   & c1 false) e

let rec unfold on e = (on (ListH.concatMap (unfold on)) & c1 [e]) e

let on_star_nary f =
  Syntax.on_star (fun a b -> f [a; b])

let on_big_star f g e =
  let rec collect e =
    (Syntax.on_star (fun e1 e2 -> (collect e1)@(collect  e2))
     & (fun e -> [e])) e in
  (Syntax.on_star (fun a b -> (f ((collect a)@(collect b))))
   & g) e


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
  let xs, ys = ac_simplify_split is_emp on_star_nary [e] in
  (mk xs, mk ys)

let mk_big_star l =
  (ac_make Syntax.mk_emp Syntax.mk_big_star @@ ac_simplify is_emp on_star_nary) l

let mk_big_or =
  ac_make (Z3.Boolean.mk_false z3_ctx) (Z3.Boolean.mk_or z3_ctx) @@
    ac_simplify Z3.Boolean.is_false Syntax.on_or

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
  let es = unfold on_star_nary e in
  List.fold_left add_if_good [] es

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

let get_lvars e =
  Syntax.ExprSet.filter Syntax.is_lvar (Syntax.vars e)

(* Returns a list of expressions e' such that lvars(e*e') includes lvars(f).
More importantly, each e' is supposed to be a good guess of how to instantiate
the variables lvars(f)-lvars(e) such that e*e' ⊢ f. *)
let guess_instances e f =
  let module VS = Syntax.ExprSet in
  let module H = Syntax.ExprHashSet in
  let get_eq_args e =
    let h = H.create 0 in
    let h_eq = H.create 0 in (* ∀x in h_eq, there is y in h s.t. x=y *)
    let add a b =
      if not (H.mem h_eq a || H.mem h_eq b) then H.add h a;
      H.add h_eq a; H.add h_eq b in
    let rec get e =
      ( Syntax.on_star (fun a b -> get a; get b)
      & Syntax.on_or (List.iter get)
      & Syntax.on_eq add
      & Syntax.on_distinct (List.iter (fun x -> add x x))
      & c1 ()) e in
    get e;
    H.fold ListH.cons h [] in
  let rec guess v f = (* finds g s.t. f contains v=g and g is not lvar *)
    let is_v = Syntax.expr_equal v in
    let do_eq a b =
      if is_v a && not (Syntax.is_lvar b)
      then Some b
      else if is_v b && not (Syntax.is_lvar a)
      then Some a
      else None in
    let do_star a b = match guess v a with None -> guess v b | g -> g in
    ( Syntax.on_star do_star
    & Syntax.on_eq do_eq
    & c1 None) f in
  let collect_guess v (gs, ws) = match guess v f with
    | None -> (gs, v :: ws)
    | Some g -> ((v, g) :: gs, ws) in
  (* HEURISTIC: Don't try to guess the values of variables inside
     spatial predicates. Instead, expect that some rule will take care
     of those predicates. *)
  let guessable_vars =
    let h = H.create 0 in
    let rec collect x =
      ( Syntax.on_var (fun v -> if Syntax.is_lvar v then H.add h v)
      & Syntax.on_const (c1 ())
      & Syntax.on_star (fun a b -> collect a; collect b)
      & Syntax.on_or (List.iter collect)
      & Syntax.on_app (fun _ es -> if Syntax.is_pure x then List.iter collect es)) x in
    collect f;
    H.fold VS.add h VS.empty in
  let vs = VS.diff guessable_vars (get_lvars e) in
  let vggs, vs = VS.fold collect_guess vs ([], []) in
  (* fprintf logf "@{vggs = %a@}@\n" (pp_list_sep "+" (pp_pair Syntax.pp_expr Syntax.pp_expr)) vggs; *)
  let bgs = get_eq_args e in
  (* fprintf logf "@{bgs = %a@}@\n" (pp_list_sep " " Syntax.pp_expr) bgs; *)
  let bgss = Misc.tuples (List.length vs) bgs in
  let rec have_same_types vl bl = match (vl, bl) with
    | [], [] -> true
    | v::vtl, b::btl ->
      if Z3.Sort.equal (Z3.Expr.get_sort v) (Z3.Expr.get_sort b)
      then have_same_types vtl btl
      else false
    | _ -> assert false in
  let bgss = List.filter (have_same_types vs) bgss in
  let vbgss = List.map (List.combine vs) bgss in
  (* fprintf logf "@{vbgss = %a@}@\n" (pp_list_sep "\n" (pp_list_sep ";" (pp_pair Syntax.pp_expr Syntax.pp_expr))) vbgss; *)
  let mk es = mk_big_star (List.map (fun (v, e) -> Syntax.mk_eq v e) es) in
  List.map mk (List.map ((@) vggs) vbgss)

let smt_implies e f =
  Syntax.is_pure e
  && Syntax.is_pure f
  && smt_is_valid (Syntax.mk_or (Syntax.mk_not e) f)

(* [smt_disprove_query] and helpers *) (* {{{ *)
exception Disproved

let disproved_hit, disproved_miss = ref 0, ref 0
module ExprPairMap = Hashtbl.Make (struct
  type t = Syntax.HashableExpr.t * Syntax.HashableExpr.t
  let equal (x1, y1) (x2, y2) =
    Syntax.HashableExpr.equal x1 x2 && Syntax.HashableExpr.equal y1 y2
  let hash (x, y) = Syntax.HashableExpr.hash x + Syntax.HashableExpr.hash y
end)
let disproved_cache = ExprPairMap.create 0

(* Raises [Disproved] when  (forall x (exists y (e(x)->f(x,y)))) is unsat. *)
let smt_disprove_query e f =
  let module VS = Syntax.ExprSet in
  try
    if ExprPairMap.find disproved_cache (e, f)
    then (incr disproved_hit; raise Disproved)
  with Not_found -> begin
    incr disproved_miss;
    let ys = VS.diff (get_lvars f) (get_lvars e) in
    let xs = VS.diff (VS.union (Syntax.vars e) (Syntax.vars f)) ys in
    let xs, ys = VS.elements xs, VS.elements ys in
    let q =
      let implies = Z3.Boolean.mk_implies Syntax.z3_ctx in
      let quant mk xs b =
        let r = mk Syntax.z3_ctx xs b None [] [] None None in
        Z3.Quantifier.expr_of_quantifier r in
      let forall = quant Z3.Quantifier.mk_forall_const in
      let exists = quant Z3.Quantifier.mk_exists_const in
      forall xs (exists ys (implies e f)) in
    Smt.push ();
(*     fprintf logf "@[<2>(DBG say %a)@]@\n@?" Syntax.pp_expr q; *)
    Smt.say q;
    let r = Smt.check_sat () in
    Smt.pop ();
    ExprPairMap.add disproved_cache (e, f) (r = Smt.Unsat);
    if r = Smt.Unsat then raise Disproved
  end

(* }}} *)

let dbg_mc = ref 0
(* }}} *)
(* Prover rules, including those provided by the user. *) (* {{{ *)
type named_rule =
  { rule_name : string (* For debug *)
  (** If (rule_apply x) is [[a;b];[c]], then a and b together are
      sufficient to prove x, and so is c alone. In particular, [[]] means
      that x was discharged, and [] means that this rule doesn't apply. If the rule
      manages to disprove x, then it should raise Disproved. *)
  ; rule_apply : Calculus.sequent -> Calculus.sequent list list
    ; rule_priority : int
    ; rule_flags : int }
let goal_discharged = [[]]
let rule_notapplicable = []

let id_rule =
  { rule_name = "identity axiom"
  ; rule_apply =
    prof_fun1 "Prover.id_rule"
    (function { Calculus.hypothesis; conclusion; _ } ->
      if Syntax.expr_equal hypothesis conclusion
      then goal_discharged
      else rule_notapplicable )
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_inconsistency lor Calculus.rule_no_backtrack }

let or_rule =
  { rule_name = "or elimination"
  ; rule_apply =
    prof_fun1 "Prover.or_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let mk_goal c = [ { Calculus.hypothesis; conclusion = c; frame } ] in
      (Syntax.on_or (List.map mk_goal) & (c1 [])) conclusion)
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_inconsistency lor Calculus.rule_no_backtrack }

let smt_pure_rule =
  { rule_name = "pure entailment (by SMT)"
  ; rule_apply =
    prof_fun1 "Prover.smt_pure_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (if not (Syntax.expr_equal conclusion Syntax.mk_emp) && smt_implies hypothesis conclusion
      then [[{ Calculus.hypothesis; conclusion = Syntax.mk_emp; frame }]]
      else rule_notapplicable ))
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_inconsistency lor Calculus.rule_no_backtrack }

(* ( H ⊢ C ) if ( H ⊢ I and H * I ⊢ C ) where
I is x1=e1 * ... * xn=en and x1,...,xn are lvars occuring in C but not H.
TODO: This rule is wrongly matching lvars from the spatial part of the
conclusion with terms from the pure part of the hypothesis. *)
let abduce_instance_rule =
  { rule_name = "guess value of lvar that occurs only on rhs"
  ; rule_apply =
    prof_fun1 "Prover.abduce_instance_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let is_or = Z3.Boolean.is_or in
      if is_or conclusion then rule_notapplicable
      else
        let _Is = guess_instances hypothesis conclusion in
        let _Is = List.filter (fun _I -> not (Syntax.expr_equal _I Syntax.mk_emp || smt_is_valid (Syntax.mk_eq _I conclusion))) _Is in
        if _Is = [] then rule_notapplicable
        else
          let mk _I =
            fprintf logf "@{[%a]@}@\n" Syntax.pp_expr _I;
            [ { Calculus.hypothesis; conclusion = _I; frame = Syntax.mk_emp }
            ; { Calculus.hypothesis = mk_star hypothesis _I; conclusion; frame } ]
          in List.map mk _Is
    )
  ; rule_priority = 999999
  ; rule_flags = Calculus.rule_instantiation }

let smt_disprove =
  { rule_name = "SMT disprove"
  ; rule_apply =
    prof_fun1 "Prover.smt_disprove"
    (function { Calculus.hypothesis; conclusion; frame } ->
      if not (Syntax.is_pure hypothesis)
      then rule_notapplicable
      else begin
        let conclusion, _ = extract_pure_part conclusion in
        smt_disprove_query hypothesis conclusion;
        rule_notapplicable
      end)
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_no_backtrack lor Calculus.rule_inconsistency }

(* A root-leaf path of the result matches ("or"?; "star"?; "not"?; OTHER).
   The '?' means 'maybe', and OTHER matches anything else other than "or", "star",
   and "not". *)
let normalize =
  let rec not_not e =
    let e = Syntax.recurse not_not e in
    (Syntax.on_not (Syntax.on_not c0 & (c1 e))
     & c0) e in
  let rec star_below_or e = (* (a∨b)*(c∨d) becomes (a*c)∨(a*d)∨(b*c)∨(b*d) *)
    let ess = List.map (unfold Syntax.on_or) (unfold on_star_nary e) in
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
let normalize = prof_fun1 "Prover.normalize" normalize

(* find_matches and helpers *) (* {{{ *)
type bindings = Z3.Expr.expr Syntax.ExprMap.t

let try_find x m = try Some (Syntax.ExprMap.find x m) with Not_found -> None

let rec instantiate bs p =
  let on_var pv =
    match try_find pv bs with None -> pv | Some e -> e in
  let on_app po ps = Z3.FuncDecl.apply po (List.map (instantiate bs) ps) in
  (Syntax.on_var on_var & Syntax.on_app on_app) p

(* TODO: Maybe rename to expr_cases2, or even Expr.cases2? *)
let cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) =
  let on_pvar pv =
    (Syntax.on_var (on_pvar_var pv)
     & Syntax.on_app (on_pvar_op pv)) e in
  let on_pop po ps =
    (Syntax.on_var (on_pop_var po ps)
     & Syntax.on_app (on_pop_op po ps)) e in
  (Syntax.on_var on_pvar & Syntax.on_app on_pop) p

let expr_match_ops go e f =
  let err _ =
    fprintf str_formatter
      "expr_match_ops %a and %a" Syntax.pp_expr e Syntax.pp_expr f;
    invalid_arg (flush_str_formatter ()) in
  cases_pat_exp (c1 err) (c2 err) (c2 err) go (e, f)

let match_args = expr_match_ops
  (fun ep es fp fs ->
    if ep <> fp then None
    else let rec go eqs es fs = match es, fs with
      | [], [] -> Some (Syntax.mk_big_star eqs)
      | [], _ | _, [] -> None
      | e :: es, f :: fs ->
          let eqs = if Syntax.expr_equal e f then eqs else Syntax.mk_eq e f :: eqs in
          go eqs es fs in
      go [] es fs)

(** Find all instantiations that make the pattern [pat] match the expression [expr]

    input [bs] is one assignment, the current branch we are exploring
    output is list of assignments, all possible extensions which leads to a match

    Parameterized by
    [eqs] : expr list, a set of equalities that are known to hold (typically, the LHS of the current sequent)
    [is_free] : expr -> bool, signifying which variables should be instantiated
    [can_be_op] : expr -> bool, signifying which variables can be instantiated not just with variables

    Assumes that [expr] does not contain pattern variables
    Assumes that [expr] and [pat] are in normal form
    Always fails when either [expr] or [pat] have top-level disjunctions

    Works best if known equalities have been pushed to Z3, so that we
    can use its congruence closure mechanism to ask if some expression
    is "trivially" equal to another efficiently. This allows matching
    between two syntactically different expressions which are equal
    because of known equalities.
*)
let rec find_matches eqs is_free can_be_op bs (pat,expr) =
  (* use Z3 congruence closure to decide equality between expressions *)
  let congruent e f = Syntax.expr_equal e f || smt_is_valid (Syntax.mk_eq e f) in
  let bind bs pv eb = match try_find pv bs with
    | None -> [Syntax.ExprMap.add pv eb bs]
    | Some e' -> if congruent eb e' then [bs] else [] in
  (** [p] and [e] are atoms, ie expressions that have neither || nor * *)
  let rec find_atom_matches bs p e =
    (* called when pattern is a variable [pv] and expression is a variable [ev] *)
    (* TODO: We might need a symmetric condition. *)
    let on_pvar_var pv ev =
      if is_free pv then bind bs pv ev
      else if Syntax.expr_equal pv ev then [bs] else [] in
    (* called when pattern is a variable [pv] and expression is an op ([o] [es]) *)
    let on_pvar_op pv o es = if can_be_op pv then bind bs pv e else [] in
    (* called when pattern is an op and expression is a variable *)
    let on_pop_var po ps ev =
      (* HEURISTIC: look for ?x = po(ps) in [expr] and use the matches
         bs' on the provision that ev = po(ps)[bs'] *)
      let p = Z3.FuncDecl.apply po ps in
      let been_there =
        (Syntax.on_star (fun f a -> Syntax.is_tpat f &&
          (Syntax.on_eq (fun x q -> Syntax.is_tpat x && Syntax.expr_equal p q)
           & c1 false) a)
          & c1 false ) pat in
      if been_there then [] (* prevent infinite loops *)
      else
        let x = Syntax.mk_fresh_tpat (Z3.FuncDecl.get_range po) "x" in
        let f = Syntax.mk_fresh_bool_tpat "f" in
        let new_pat = Syntax.mk_star f (Syntax.mk_eq x p) in
        (* fprintf logf "@[Trying to find %a = %a in %a@]@\n" Syntax.pp_expr ev Syntax.pp_expr p (pp_list_sep "*" Syntax.pp_expr) eqs; *)
        let new_bs = find_matches eqs is_free can_be_op bs (new_pat, Syntax.mk_big_star eqs) in
        let is_good b =
          let p = instantiate b p in
          (* fprintf logf "@[found a candidate: %a@]@\n" Syntax.pp_expr p; *)
          congruent ev p in
        List.filter is_good new_bs in
    (* called when pattern is an op ([po] [ps]) and expression is an op ([o] [es]) *)
    let on_pop_op po ps o es =
      if (not (Z3.FuncDecl.equal po o)) || List.length ps <> List.length es
      then []
      else
        let todos = List.combine ps es in
        let process_todo acc (tp, te) =
          let atom bs =
            let new_bs = flip ((flip find_atom_matches) tp) te bs in
            if Z3.Boolean.is_eq (Z3.FuncDecl.apply po ps) then
              let (p1, p2) = match ps with [x; y] -> x, y | _ -> assert false in
              let f bs =
                not (Syntax.expr_equal (instantiate bs p1) (instantiate bs p2)) in
              List.filter f new_bs
            else new_bs in
          acc >>= atom in
        List.fold_left process_todo [bs] todos in
    cases_pat_exp on_pvar_var on_pvar_op on_pop_var on_pop_op (p, e) in
  (** matches bigstar of [el] against bigstar of [pl] under bindings [bs] *)
  let find_star_matches bs pl el =
    let (tpatvars, patoms)  = List.partition Syntax.is_tpat pl in
    if List.length tpatvars > 1 then
      failwith "pattern formulas should have at most one formula variable (qj979xyr)";
    (** matches a pattern [p] against a list of *-conjoined
        expressions el. Returns a list of pairs (b',el') of matching
        bindings b' together with leftover expressions el' *)
    let rec one_patom bs acc p = function
      | [] -> [] (* no match *)
      | e::tl ->
        let bs' = find_atom_matches bs p e in
        if bs' = [] then one_patom bs (e::acc) p tl
        else (bs', (List.rev acc)@tl)::one_patom bs (e::acc) p tl in
    let f ebl p =
      let g (bss, es) = bss >>= (fun bs' -> one_patom bs' [] p es) in
      ebl >>= g in
    let atom_matches = List.fold_left f [([bs], el)] patoms in
    if tpatvars = [] then
      atom_matches >>=
        (fun (bss, es) ->
          bss >>= fun bs -> if es = [] then [bs] else [])
    else
      let tpatvar = List.hd tpatvars in
      (* at most one pattern variable, which gets the leftover frame *)
      atom_matches >>=
        (fun (bss, es) ->
          bss >>= fun bs -> bind bs tpatvar (Syntax.mk_big_star es)) in
  let no_star pa =
    let fsm = find_star_matches bs [pa] in
    (on_big_star fsm
     & fun _ -> fsm [expr]) expr in
  let star pl =
    let fsm = find_star_matches bs pl in
    (on_big_star fsm
     & fun _ -> fsm [expr]) expr in
  (* fprintf logf "@{Matching %a to %a@}@?@\n" Syntax.pp_expr p Syntax.pp_expr e; *)
  let r = (on_big_star star & no_star) pat in
  (* let pp_binding f b = *)
  (*   fprintf f "@{Found matches:@\n@{<v 2>%a@}@}@?@\n" (pp_list (pp_pair Syntax.pp_expr Syntax.pp_expr)) (Syntax.ExprMap.fold (fun pat ex l -> (pat,ex)::l) b []) in *)
  (* fprintf logf "@{<v 2>%a@}" (pp_list pp_binding) r; *)
  r
let find_matches = prof_fun4 "Prover.find_matches" find_matches

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
                  let cp = Syntax.mk_star cp p in
                  if smt_is_valid (Syntax.mk_not (Syntax.mk_star hp cp))
                  then gs
                  else list_spatial_matches gs hp cp (h :: fs) nhs hs (ds @ cs)) in
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
let find_existential_matches =
  find_matches [] Syntax.is_lvar (c1 false)

let find_existential_sub_matches leftover_var =
  find_matches [] Syntax.is_lvar (Syntax.expr_equal leftover_var)

(*
let find_existential_match = find_conversion Syntax.is_lvar
*)

let spatial_id_rule =
  { rule_name = "spatial parts match"
  ; rule_apply =
    prof_fun1 "Prover.spatial_id_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      (* if log log_prove then fprintf logf "hp: %a@ hs: %a@ cp: %a@ cs: %a"
        Syntax.pp_expr hyp_pure Syntax.pp_expr hyp_spatial Syntax.pp_expr conc_pure Syntax.pp_expr conc_spatial;*)
      if Syntax.expr_equal hyp_spatial Syntax.mk_emp
        && Syntax.expr_equal conc_spatial Syntax.mk_emp
      then rule_notapplicable
      else if Syntax.expr_equal hyp_spatial conc_spatial (* should really be handled by matching *)
      then [[{ Calculus.hypothesis = hyp_pure; conclusion = conc_pure; frame}]]
      else begin
        let matches = find_existential_matches Syntax.ExprMap.empty (conc_spatial, hyp_spatial) in
        if log log_prove then fprintf logf "@,found %d matches@," (List.length matches);
        let mk_goal m =
          let b = Syntax.ExprMap.bindings m in
          let mk_eq (v, e) = Z3.Boolean.mk_eq z3_ctx v e in
          [ { Calculus.hypothesis = hyp_pure
            ; conclusion = mk_big_star (conc_pure :: List.map mk_eq b)
            ; frame } ] in
        List.map mk_goal matches
      end)
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_no_backtrack }

let match_rule =
  { rule_name = "matching free variables"
  ; rule_apply =
    prof_fun1 "Prover.match_rule"
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
      List.map mk_goal matches)
  ; rule_priority = 100
  ; rule_flags = 0 }

let match_subformula_rule =
  { rule_name = "matching spatial subformula"
  ; rule_apply =
    prof_fun1 "Prover.match_subformula_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      let hyp_pure, hyp_spatial = extract_pure_part hypothesis in
      let conc_pure, conc_spatial = extract_pure_part conclusion in
      if Syntax.expr_equal Syntax.mk_emp conc_spatial
      then rule_notapplicable else begin
        let lo_name = "_leftover" in
        let leftover = Syntax.mk_bool_lvar lo_name in
        let enhanced_conc = Syntax.mk_star leftover conc_spatial in
        let matches =
          find_existential_sub_matches leftover Syntax.ExprMap.empty (enhanced_conc, hyp_spatial) in
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
          [ [ { Calculus.hypothesis = mk_star leftover_match hyp_pure
              ; conclusion = conc_pure
              ; frame = mk_star frame conc_spatial } ] ] in
        matches >>= mk_goal
      end)
  ; rule_priority = 100
  ; rule_flags = 0 }

(* This is intended as a lightweight version of [match_subformula_rule]. *)
let spatial_match_rule =
  { rule_name = "spatial match (lightweight)"
  ; rule_apply =
    prof_fun1 "Prover.spatial_match_rule"
    (function { Calculus.hypothesis; conclusion; frame } ->
      (* TODO: don't apply rule if hyp & conc have disjunctions. *)
      let hyp_pure, hs = ac_simplify_split is_emp on_star_nary [hypothesis] in
      let conc_pure, cs = ac_simplify_split is_emp on_star_nary [conclusion] in
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
      List.map (fun x -> [x]) gs)
  ; rule_priority = 100
  ; rule_flags = Calculus.rule_inconsistency }

let find_pattern_matches eqs = find_matches eqs (c1 true) Syntax.is_tpat

let add_sequent_eqs s =
  let rec add_eqs e =
    ( Syntax.on_eq (fun _ _ -> (Smt.say e); [e])
    & Syntax.on_star (fun a b -> add_eqs a@add_eqs b)
    & (c1 [])) e in
  add_eqs s.Calculus.hypothesis

let find_sequent_matches bs ps s =
  Smt.push ();
  let eqs = add_sequent_eqs s in
  let fm pat exp bs = find_pattern_matches eqs bs (pat, exp) in
  (* OPTIM: match less expensive things first.
     A lot of rules won't match and we need to discover the ones which
     don't as fast as possible. *)
  (* TODO: This ordering is just a heuristic, it could be improved by
     actually measuring the sizes of the formules in [s] *)
  let r =
    fm ps.Calculus.conclusion s.Calculus.conclusion bs >>=
      fm ps.Calculus.frame s.Calculus.frame >>=
      fm ps.Calculus.hypothesis s.Calculus.hypothesis in
  Smt.pop ();
  r

(** Applies rewrite rule [r] everywhere in [e]

    not recursively though: rewriting could trigger more
    rewriting. That is not taken into account. This is because to do
    it properly we would need to do a fix point over all the rewrite
    rules, not just one. This happens in [rw_of_rules].
*)
let rec rewrite_in_expr eqs r e =
  let name = r.Calculus.rw_name in
  let from_pat = r.Calculus.rw_from_pattern in
  let to_pat = r.Calculus.rw_to_pattern in
  let op = Z3.Expr.get_func_decl from_pat in
  let rewrite_op e =
    let bs = find_pattern_matches eqs Syntax.ExprMap.empty (from_pat, e) in
    if bs = [] then e
    else (
      assert (List.length bs = 1); (* Jules: is this reasonable? *)
      let f = instantiate (List.hd bs) to_pat in
      if log log_prove then
        fprintf logf "@{<p>Rewrote %s: @[%a@] -> @[%a@]@}@\n" name Syntax.pp_expr e Syntax.pp_expr f;
      f) in
  (Syntax.on_op op (fun _ -> rewrite_op e)
   & Syntax.on_app (fun op l ->
     Z3.FuncDecl.apply op (List.map (rewrite_in_expr eqs r) l))) e

(* }}} *)

let instantiate_sequent bs s =
  { Calculus.frame = instantiate bs s.Calculus.frame
  ; hypothesis = instantiate bs s.Calculus.hypothesis
  ; conclusion = instantiate bs s.Calculus.conclusion }

let builtin_rules =
  [ id_rule
  ; smt_pure_rule
  ; smt_disprove
  ; spatial_id_rule
  (* ; spatial_match_rule (* should be before abduce_instance_rule *) *)
  (* ; or_rule *)
  (* ; match_rule (\* XXX: subsumed by match_subformula_rule? *\) *)
  (* ; match_subformula_rule *)
  ; abduce_instance_rule
  ]

(* FIXME: should freshen free logical variables in seq_subgoal_pattern
   and rw_to_pattern patterns *)
(* TODO: normalize rule patterns (perhaps best done earlier as this is called often-ish *)
let rules_of_calculus rw =
  let apply_seq_schema rs s = (* RLP: Should we refer to some bindings here? *)
    let check bs c = smt_is_valid (rw s (instantiate bs c)) in
    let is_fresh bs (v, e) =
      not (Syntax.ExprSet.exists (Syntax.expr_equal v) (Syntax.vars (instantiate bs e))) in
    let side_conditions s freshs checks bs =
      List.for_all (is_fresh bs) freshs
      && List.for_all (check bs) checks in
    let m = find_sequent_matches Syntax.ExprMap.empty rs.Calculus.seq_goal_pattern s in
    let sc = side_conditions s rs.Calculus.seq_fresh_in_expr rs.Calculus.seq_pure_check in
    let mm = m in
    let m = List.filter sc m in
    if log log_prove && m = [] && mm <> [] then fprintf logf "@{side conditions failed@}@?@\n";
    let try_one bs =
      List.map (instantiate_sequent bs) rs.Calculus.seq_subgoal_pattern in
    if m != [] then
      if Calculus.is_no_backtrack_rule rs.Calculus.seq_flags then
        (* if no backtrack then just pick one instantiation *)
        [try_one (List.hd m)]
      else
        List.map try_one m
    else rule_notapplicable in
  let rule_of_seq_schema rs =
    { rule_name = rs.Calculus.seq_name
    ; rule_apply = prof_fun1 ("user-"^rs.Calculus.seq_name) (apply_seq_schema rs)
    ; rule_priority = rs.Calculus.seq_priority
    ; rule_flags = rs.Calculus.seq_flags } in
  List.map rule_of_seq_schema

let rw_of_rules rss s e =
  Smt.push ();
  let eqs = add_sequent_eqs s in
  let rec apply e = function
    | [] -> e
    | rs::tl ->
      let f = rewrite_in_expr eqs rs e in
      if Syntax.expr_equal e f then apply e tl
      else apply f rss in
  let r = apply e rss in
  Smt.pop ();
  r


(* }}} *)
(* The main proof-search algorithm. *) (* {{{ *)

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with
with score [> Backtrack.max_penalty] needs a proof.  Anything in-between is kind
of acceptable as a leaf, but we should keep looking for something better.
  TODO: we may want min_penalty and max_penalty decrease with the level n
  TODO: we may want to count only once a leaf appearing twice
  TODO: we may want to partly cache the results of proving
*)
let rec solve rw rules penalty n goal =
  if log log_prove then fprintf logf "@[<2>@{<details>";
  let goal =
    { Calculus.frame = normalize goal.Calculus.frame
    ; hypothesis = normalize (rw goal goal.Calculus.hypothesis)
    ; conclusion = normalize (rw goal goal.Calculus.conclusion) } in
  if log log_prove then fprintf logf "@{<summary>goal@@%d:@} @{<p>%a@}@," n CalculusOps.pp_sequent goal;
  let leaf = ([goal], penalty n goal) in
  if log log_prove then fprintf logf "@{<p>Current goal has penalty %d at level %d@}@\n" (penalty n goal) n;
  let result =
    if n = 0 then leaf else begin
      let btrackable r = not (Calculus.is_no_backtrack_rule r.rule_flags) in
      let process_rule r =
        if log log_prove then fprintf logf "@{<p>apply rule %s@}@?@\n" r.rule_name;
        let ess = r.rule_apply goal in
        if ess = rule_notapplicable then raise Backtrack.No_match;
        if safe then assert (List.for_all (List.for_all (not @@ Calculus.sequent_equal goal)) ess);
        if log log_prove then fprintf logf "@{<p> applied.@}@?@\n";
        ess in
      let solve_subgoal = solve rw rules penalty (n - 1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal (c1 true) ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals (c1 true) leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      try choose_rule btrackable leaf rules
      with Disproved -> begin
        if log log_prove then fprintf logf "disproved@\n";
        leaf
      end
    end in
  if log log_prove then fprintf logf "@}@]@\n";
  result

let solve_idfs min_depth max_depth rw rules penalty goal =
  if log log_prove then fprintf logf "@[<2>@{<details>@{<summary>start idfs proving@}@\n";
  let solve = flip (solve rw rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve (c1 true) give_up succ fail min_depth in
  if log log_prove then fprintf logf "@}@]@\n@?";
  r

(* }}} *)
(* Penalty functions. *) (* {{{ *)

let rec heap_size e =
  if Syntax.is_pure e then 0 else
  ( Syntax.on_not heap_size
  & Syntax.on_or (List.fold_left max 0 @@ List.map heap_size)
  & Syntax.on_star (fun a b -> heap_size a + heap_size b)
  & c1 1) e

(* }}} *)
(* The top level interface. *) (* {{{ *)

let min_depth = 2
let max_depth = 6

let wrap_calculus flags f calculus =
  let filt (sqr,rwr) = function
    | Calculus.Sequent_rule r -> (r::sqr,rwr)
    | Calculus.Rewrite_rule r -> (sqr,r::rwr) in
  let (seq_rules, rw_rules) = List.fold_left filt ([],[]) calculus in
  (* order has been flipped by fold on [filt], restore it *)
  let rw = rw_of_rules (List.rev rw_rules) in
  let user_filter r = flags r.Calculus.seq_flags in
  let user_rules = rules_of_calculus rw (List.filter user_filter seq_rules) in
  (* order has been flipped by fold on [filt], restore it *)
  let user_rules = List.rev user_rules in
  let filter r = flags r.rule_flags in
  let rules = List.filter filter builtin_rules in
  let cmp_rules r1 r2 = compare r1.rule_priority r2.rule_priority in
  let rules = List.stable_sort cmp_rules (rules @ user_rules) in
  f rw rules

let is_entailment rw rules lhs rhs =
  let penalty _ { Calculus.hypothesis; conclusion; _ } =
    if Syntax.expr_equal conclusion Syntax.mk_emp && Syntax.is_pure hypothesis
    then 0
    else Backtrack.max_penalty in
  let goal =  { Calculus.hypothesis = lhs; conclusion = rhs; frame = Syntax.mk_emp } in
  let _, p = solve_idfs min_depth max_depth rw rules penalty goal in
  p = 0
let is_entailment = prof_fun3 "Prover.is_entailment" is_entailment

let infer_frame rw rules lhs rhs =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    if is_instantiation conclusion
    then (n + 1) * heap_size hypothesis
    else Backtrack.max_penalty in
  let goal =  { Calculus.hypothesis = lhs; conclusion = rhs; frame = Syntax.mk_emp } in
  let ss, p = solve_idfs min_depth max_depth rw rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []
let infer_frame = prof_fun3 "Prover.infer_frame" infer_frame

let biabduct rw rules lhs rhs =
  let penalty n { Calculus.hypothesis; conclusion; _ } =
    (n + 1) * (heap_size hypothesis + heap_size conclusion) in
  let goal =  { Calculus.hypothesis = lhs; conclusion = rhs; frame = Syntax.mk_emp } in
  let ss, p = solve_idfs min_depth max_depth rw rules penalty goal in
  if p < Backtrack.max_penalty then afs_of_sequents ss else []
let biabduct = prof_fun3 "Prover.biabduct" biabduct

let is_inconsistent rw rules e =
  is_entailment rw rules e (Z3.Boolean.mk_false z3_ctx)
let is_inconsistent = prof_fun2 "Prover.is_inconsistent" is_inconsistent

let is_entailment = wrap_calculus (fun f -> (not @@ Calculus.is_abduct_rule) f && (not @@ Calculus.is_instantiation_rule) f) is_entailment
let infer_frame = wrap_calculus (not @@ Calculus.is_abduct_rule) infer_frame
let biabduct = wrap_calculus (c1 true) biabduct
let is_inconsistent = wrap_calculus Calculus.is_inconsistency_rule is_inconsistent

let print_stats () =
  if log log_stats then
    fprintf logf "disproved_hit %d disproved_miss %d@\n" !disproved_hit !disproved_miss
(* }}} *)
