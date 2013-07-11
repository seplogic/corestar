(********************************************************
   This file is part of coreStar
        src/prover/clogic.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Debug
open Format

(* TODO(rgrig): Don't open these. *)
open Cterm
open Misc
open Printing
open Psyntax

module CC = Congruence.CC

exception Success
exception Failed
exception Assm_Contradiction

module RMSet = Multiset.Make(
  struct
    type t = string * Cterm.term_handle
    let compare = compare
  end
)

type multiset = RMSet.multiset

module SMSet = Multiset.Make(
  struct
    type t = string * (Psyntax.args list)
    let compare = compare
  end
)

type syntactic_form =
  {
   sspat : SMSet.multiset;
   splain : SMSet.multiset;
   sdisjuncts : (syntactic_form * syntactic_form) list;
   seqs : (Psyntax.args * Psyntax.args) list;
   sneqs : (Psyntax.args * Psyntax.args) list;
  }

type formula =
  {
    spat : RMSet.multiset;
    plain : RMSet.multiset;
    disjuncts : (formula * formula) list;
    eqs : (term_handle * term_handle) list;
    neqs : (term_handle * term_handle) list;
  }

type ts_formula =
  { ts : Cterm.term_structure
  ; form : formula }

let dump_rmset ts =
  RMSet.iter
    (fun (n, i) ->
      match Cterm.get_pargs false ts [] i with
	| Arg_op ("tuple", x) ->
          printf "@[Tuple application: %s to %a = (%a)@\n@]@?"
	    n
	    (Cterm.pp_c_raw ts) i
	    (pp_list_sep ", " Psyntax.string_args) x;
	| x ->
          printf "@[Non-tuple application: %s to %a = %a@\n@]@?"
	    n
	    (Cterm.pp_c_raw ts) i
	    Psyntax.string_args x; assert false)

let rec check_ts_formula tsf =
  let check_constant c = assert (Cterm.equal tsf.ts c c) in
  let iter_pair f (a, b) = f a; f b in
  List.iter (iter_pair check_constant) tsf.form.eqs;
  List.iter (iter_pair check_constant) tsf.form.neqs;
  let check_formula form = check_ts_formula {tsf with form} in
  List.iter (iter_pair check_formula) tsf.form.disjuncts;
(* DBG  dump_rmset tsf.ts tsf.form.spat; *)
(* DBG  dump_rmset tsf.ts tsf.form.plain; *)
  ()

let rec check_consistent_ts_formula tsf =
  let check_constant c = assert (Cterm.equal tsf.ts c c) in
  let iter_pair f (a, b) = f a; f b in
  List.iter (iter_pair check_constant) tsf.form.eqs;
  List.iter (iter_pair check_constant) tsf.form.neqs;
  (try List.iter (fun (x,y) -> ignore (make_equal tsf.ts x y)) tsf.form.eqs
  with Psyntax.Contradiction -> assert false);
  (try List.iter (fun (x,y) -> ignore (make_not_equal tsf.ts x y)) tsf.form.neqs
  with Psyntax.Contradiction -> assert false);
  let check_formula form = check_consistent_ts_formula {tsf with form} in
  List.iter (iter_pair check_formula) tsf.form.disjuncts

let mk_ts_form ts form =
  {ts = ts; form = form;}

let break_ts_form ts_form =
  ts_form.ts, ts_form.form

let kill_var ts_form v =
  {ts_form with ts = Cterm.kill_var ts_form.ts v}

let freshen_exists (v, ts_form) =
  let v, ts = Cterm.freshen_exists (v, ts_form.ts) in
  (v, {ts_form with ts})

let update_var_to ts_form v e =
  {ts_form with ts = Cterm.update_var_to ts_form.ts v e}

(* {{{ pretty printing
 * See
 *   http://rgrig.blogspot.com/2010/09/certain-type-of-pretty-printing-in.html
 * for an explanation of the basic idea.  *)
(* {{{ printing of atomic formulas *)
(* TODO(rgrig): What's a better name for RMSet.t and SMSet.t? *)
let pp_rmset_element prefix pp_term ppf (s, t) =
  fprintf ppf "@[%s%s(%a)@]" prefix s pp_term t

let pp_smset_element prefix ppf (n, args) =
  fprintf ppf "@[%s%s(%a)@]" prefix n string_args_list args

(* }}} *)
(* {{{ printing for [formula], [syntactic_form], and [ts_form] *)
(* NOTE: The pattern match on formula is meant to cause errors if
  * new fields are added to type [formula]. *)
let rec pp_formula' pp_term pp ppf first
  {spat=spat; plain=plain; disjuncts=disjuncts; eqs=eqs; neqs=neqs} =
    let first =
      List.fold_left (pp.separator (pp_eq pp_term) ppf) first eqs in
    let first =
      List.fold_left (pp.separator (pp_neq pp_term) ppf) first neqs in
    let first =
      RMSet.fold (pp.separator (pp_rmset_element "" pp_term) ppf) first spat in
    let first =
      RMSet.fold (pp.separator (pp_rmset_element "!" pp_term) ppf) first plain
    in
      List.fold_left
        (pp.separator (pp_disjunct (pp_formula pp_term)) ppf) first disjuncts
and pp_formula pp_term = pp_whole (pp_formula' pp_term) pp_star

let rec pp_syntactic_form' pp ppf first
  {sspat=sspat; splain=splain; sdisjuncts=sdisjuncts; seqs=seqs; sneqs=sneqs} =
    let first =
      List.fold_left (pp.separator (pp_eq string_args) ppf) first seqs in
    let first =
      List.fold_left (pp.separator (pp_neq string_args) ppf) first sneqs in
    let first =
      SMSet.fold (pp.separator (pp_smset_element "") ppf) first sspat in
    let first =
      SMSet.fold (pp.separator (pp_smset_element "!") ppf) first splain
    in
      List.fold_left
        (pp.separator (pp_disjunct pp_syntactic_form) ppf) first sdisjuncts
and pp_syntactic_form ppf sform = pp_whole pp_syntactic_form' pp_star ppf sform

let pp_ts_formula' pp ppf first {ts=ts; form=form} =
  let first = Cterm.pp_ts' pp ppf first ts in
  pp_formula' (pp_c ts) pp ppf first form

let pp_ts_formula = pp_whole pp_ts_formula' pp_star

(* }}} *)
(* pretty printing }}} *)

let conjunction form1 form2 : formula =
  {
  spat = RMSet.union form1.spat form2.spat;
  plain = RMSet.union form1.plain form2.plain;
  disjuncts = form1.disjuncts @ form2.disjuncts;
  eqs = form1.eqs @ form2.eqs;
  neqs = form1.neqs @ form2.neqs;
}

let disjunction form1 form2 : formula =
  {
  spat = RMSet.empty;
  plain = RMSet.empty;
  disjuncts = [(form1,form2)];
  eqs =[];
  neqs = [];
}

let empty : formula =
  {
  spat = RMSet.empty;
  plain = RMSet.empty;
  disjuncts = [];
  eqs = [];
  neqs = [];
}

let false_sform =
  {
  sspat = SMSet.empty;
  splain = SMSet.from_list [("@False",[])];
  sdisjuncts = [];
  seqs = [];
  sneqs = [];
}

let is_sempty s =
  s.sspat = SMSet.empty &&
  s.splain = SMSet.empty &&
  s.sdisjuncts = [] &&
  s.seqs = [] &&
  s.sneqs = []

let truth = empty

let is_true form =
  form.spat = RMSet.empty
    && form.plain = RMSet.empty
    && form.disjuncts = []
    && form.eqs = []
    && form.neqs = []


let add_eqs_t_list fresh eqs ts : term_structure =
  List.fold_left (fun ts (x,y) ->
    try
      make_equal_t fresh ts x y
    with Contradiction -> begin
      if log log_logic then begin
        fprintf logf "@[<2>Trying to make %a and %a equal failed.@]@\n"
          string_args x string_args y
      end;
      raise Contradiction
    end) ts eqs

let add_neqs_t_list fresh neqs ts : term_structure =
  List.fold_left (fun ts (x,y) ->
    try
      make_not_equal_t fresh ts x y
    with Contradiction -> begin
      if log log_logic then begin
        fprintf logf "@[<2>Trying to make %a and %a not equal failed.@]@\n"
          string_args x string_args y
      end;
      raise Contradiction
    end) ts neqs

let add_eqs_list eqs ts : term_structure =
  List.fold_left (fun ts (x,y) -> make_equal ts x y) ts eqs

let add_neqs_list neqs ts : term_structure =
  List.fold_left (fun ts (x,y) -> make_not_equal ts x y) ts neqs


  (* As multiple term_handles might be equal,
     we have to use a comparison based only on the predicate name.
     The sorting means predicates with the same name will be next
     to each other. *)
let intersect_with_ts ts rem_snd set1 set2 =
  let rec match_same rem_snd set1 set2 intersect count =
    if RMSet.has_more set1 && RMSet.has_more set2 then
      let c1,nset1 = RMSet.remove set1 in
      let c2,nset2 = RMSet.remove set2 in
      let cmp = compare (fst c1) (fst c2) in
      if cmp = 0 then
	if Cterm.equal ts (snd c1) (snd c2) then
	  let nset2 = (if rem_snd then nset2 else set2) in
	  match_same rem_snd nset1 (RMSet.back nset2 count) (c2::intersect) 0
	else
	    (* Not a match, try next. *)
	  match_same rem_snd set1 (RMSet.next set2) intersect (count+1)
      else if cmp < 0 then
	  (* First set is a low one, so skip element,
	     reverse second set over similar elements in case next element is same class*)
	match_same rem_snd (RMSet.next set1) (RMSet.back set2 count) intersect 0
      else
	  (* Second set has lowest element, so skip element *)
	match_same rem_snd set1 (RMSet.next set2) intersect 0
    else
	(* No more left to match *)
      (RMSet.from_list intersect, RMSet.restart set1, RMSet.restart set2)
  in
  match_same rem_snd set1 set2 [] 0



let rec normalise ts form : formula * term_structure =
(*  printf "Normalising formula : %a @\n" pp_ts_form  {ts=ts;form=form};*)
  let rec f nform ts disj =
    match disj with
      [] -> nform,ts
    | (f1,f2)::disj ->
	let f1o =
	  try
	    let ts1 = add_eqs_list f1.eqs ts in
	    let ts1 = add_neqs_list f1.neqs ts1 in
	    let f1,ts1 = normalise ts1 f1 in
	    Some (f1,ts1)
	  with Contradiction ->
	    printf "Contradiction left@\n"; (* DBG *)
	    None in
	let f2o =
	  try
	    let ts2 = add_eqs_list f2.eqs ts in
	    let ts2 = add_neqs_list f2.neqs ts2 in
	    let f2,ts2 = normalise ts2 f2 in
	    Some (f2,ts2)
	  with Contradiction ->
            printf "Contradiction right@\n"; (* DBG *)
	    None in
	match f1o,f2o with
	  None,None -> raise Contradiction
	| Some (form,ts'), None
	| None, Some (form,ts') ->
            if log log_logic then begin
              fprintf logf
                "@[<2>Disjunct eliminated! Remaining disjunct:@ %a@]@\n"
                (pp_formula (pp_c ts)) form
            end;
	    let nform = (conjunction form nform) in
	    f nform
	      ts'
	      disj
	| Some (f1,_),Some (f2,_) ->
	    let s,s1,s2 = intersect_with_ts ts true f1.spat f2.spat in
	    let p,p1,p2 = intersect_with_ts ts true f1.plain f2.plain in
	    let f1 = {f1 with spat=s1;plain=p1} in
	    let f2 = {f2 with spat=s2;plain=p2} in
	    f
	      {nform with
	       spat = RMSet.union s nform.spat;
	       plain = RMSet.union p nform.plain;
	       disjuncts =
	       if is_true(f1) || is_true(f2) then
		 nform.disjuncts
	       else
		 ((f1,f2)::nform.disjuncts)
	     }
	      ts
	      disj
  in
  let form,ts = f {form with disjuncts=[]} ts form.disjuncts in
(*  printf "Normalised formula : %a @\n" pp_ts_form  {ts=ts;form=form};*)
  form,ts


let rec convert_to_inner (form : Psyntax.pform) : syntactic_form =
  let convert_atomic_to_inner (sspat,splain,sdisj,seqs,sneqs) pat =
    match pat with
      P_EQ (a1,a2) -> sspat, splain,sdisj,(a1,a2)::seqs, sneqs
    | P_NEQ (a1,a2) -> sspat, splain,sdisj,seqs, (a1,a2)::sneqs
    | P_PPred (name, al) -> sspat, ((name, al)::splain),sdisj,seqs,sneqs
    | P_SPred (name, al) -> ((name,al)::sspat), splain,sdisj,seqs,sneqs
    | P_Wand _ | P_Septract _
    | P_False -> sspat, (("@False", [])::splain),sdisj,seqs,sneqs
    | P_Or(f1,f2) ->
      let f1 = convert_to_inner f1 in
      let f2 = convert_to_inner f2 in
      sspat, splain, (f1,f2)::sdisj, seqs, sneqs
  in
  let (sspat,splain,sdisj,seqs,sneqs) = List.fold_left convert_atomic_to_inner ([],[],[],[],[]) form in
  {
   sspat = SMSet.from_list sspat;
   splain = SMSet.from_list splain;
   sdisjuncts = sdisj;
   seqs = seqs;
   sneqs = sneqs;
  }


let rec convert_to_pform { sspat; splain; sdisjuncts; seqs; sneqs } =
  let eqs = List.map (fun (a1, a2) -> P_EQ (a1, a2)) seqs in
  let neqs = List.map (fun (a1, a2) -> P_NEQ (a1, a2)) sneqs in
  let plain = List.map (fun (s,a) -> P_PPred (s,a)) (SMSet.to_list splain) in
  let spat = List.map (fun (s,a) -> P_SPred (s,a)) (SMSet.to_list sspat) in
  let disjuncts = List.map (fun (f1, f2) -> P_Or (convert_to_pform f1, convert_to_pform f2)) sdisjuncts in
  eqs @ neqs @ plain @ spat @ disjuncts


let smset_to_list fresh a ts =
  let a = SMSet.restart a in
  let rec inner a rs ts =
    if SMSet.has_more a then
      let (n,tl),a = SMSet.remove a in
      let c,ts = add_tuple fresh tl ts in
      inner a ((n,c)::rs) ts
    else
      rs, ts
  in inner a [] ts


let rec add_pair_list fresh xs ts rs =
  match xs with
    [] -> rs,ts
  | (a,b) ::xs ->
      let c1,ts = add_term fresh a ts in
      let c2,ts = add_term fresh b ts in
      add_pair_list fresh xs ts ((c1,c2)::rs)


(* TODO: Equalities in disjuncts are ignored. Is this sound on the rhs of
 entailments? If so, explain why; otherwise, fix. *)
let rec convert_sf fresh (ts :term_structure) (sf : syntactic_form) : formula * term_structure =
  let spat, ts = smset_to_list fresh sf.sspat ts in
  let plain, ts = smset_to_list fresh sf.splain ts in
  let disj, ts  = convert_sf_pair_list fresh ts sf.sdisjuncts [] in
  let ts = add_eqs_t_list fresh sf.seqs ts in
  let ts = add_neqs_t_list fresh sf.sneqs ts in
  {spat = RMSet.from_list spat; plain = RMSet.from_list plain; disjuncts = disj;eqs=[];neqs=[]}, ts
and convert_sf_without_eqs
 fresh (ts :term_structure) (sf : syntactic_form) : formula * term_structure =
  let spat, ts = smset_to_list fresh sf.sspat ts in
  let plain, ts = smset_to_list fresh sf.splain ts in
  let disj, ts  = convert_sf_pair_list fresh ts sf.sdisjuncts [] in
  let eqs,ts = add_pair_list fresh sf.seqs ts [] in
  let neqs,ts = add_pair_list fresh sf.sneqs ts [] in
  {spat = RMSet.from_list spat; plain = RMSet.from_list plain; disjuncts = disj;
  eqs=eqs;neqs=neqs}, ts
and convert_sf_pair_list
    fresh (ts :term_structure)
    (sf : (syntactic_form * syntactic_form) list)
    (rs : (formula * formula) list)
  : ((formula * formula) list) * term_structure =
  match sf with
    [] -> rs,ts
  | (x,y)::sf ->
      let x,ts = convert_sf_without_eqs fresh ts x in
      let y,ts = convert_sf_without_eqs fresh ts y in
      convert_sf_pair_list fresh ts sf ((x,y)::rs)


(* convert to a formula with all pattern variables converted to ground *)
let smset_to_list_ground a ts =
  let a = SMSet.restart a in
  let rec inner a rs ts =
    if SMSet.has_more a then
      let (n,tl),a = SMSet.remove a in
      let c,ts = ground_pattern_tuple tl ts in
      inner a ((n,c)::rs) ts
    else
      rs, ts
  in inner a [] ts

let rec convert_ground (ts :term_structure) (sf : syntactic_form) : formula * term_structure =
  assert (sf.sdisjuncts = []);  (* don't want disjuncts in an SMT pattern *)
  assert (sf.sspat = SMSet.empty);
  let plain, ts = smset_to_list_ground sf.splain ts in
  let eqs, ts = List.fold_left (fun (eqs,ts) (x,y) -> let cx,ts = ground_pattern x ts in let cy,ts = ground_pattern y ts in ((cx,cy)::eqs,ts)) ([],ts) sf.seqs in
  let neqs, ts = List.fold_left (fun (neqs,ts) (x,y) -> let cx,ts = ground_pattern x ts in let cy,ts = ground_pattern y ts in ((cx,cy)::neqs,ts)) ([],ts) sf.sneqs in
  {spat = RMSet.empty; plain = RMSet.from_list plain; disjuncts = []; eqs=eqs; neqs=neqs}, ts


(* deprecated *)
let conjoin fresh (f : ts_formula) (sf : syntactic_form) =
  let form, ts = convert_sf fresh f.ts sf in
  let form = conjunction form f.form in
  { ts; form }

let substitute_in_rmset subst xs =
  let xs = RMSet.to_list xs in
  let xs = List.map (fun (n, h) -> (n, subst h)) xs in
  RMSet.from_list xs

let rec substitute_in_formula subst { spat; plain; disjuncts; eqs; neqs } =
  let map_pair_list f = List.map (fun (x, y) -> (f x, f y)) in
  { spat = substitute_in_rmset subst spat
  ; plain = substitute_in_rmset subst plain
  ; disjuncts = map_pair_list (substitute_in_formula subst) disjuncts
  ; eqs = map_pair_list subst eqs
  ; neqs = map_pair_list subst neqs }

let conjoin_inner ts1 ts2 =
  if safe then check_ts_formula ts1;
  if safe then check_ts_formula ts2;
  let subst, ts = Cterm.conjoin ts1.ts ts2.ts in
  let ts1_form = substitute_in_formula subst ts1.form in
  let form = conjunction ts1_form ts2.form in
  { ts; form }

(* TODO(rgrig): It should be unnecessary to call this function. *)
let make_syntactic' get_eqs get_neqs ts_form =
  let ts,form = break_ts_form ts_form in
  let eqs = get_eqs ts in
  let neqs = get_neqs ts in
  let get_term = Cterm.reconstruct ts in

  let rec form_to_syntax form =
    let convert_tuple r =
      match get_term r with
        Psyntax.Arg_op("tuple",al) -> al
      | x -> printf "@[Not a tuple: %a@\n@]@?" Psyntax.string_args x; assert false in
    let convert_pair = lift_pair get_term in
    let eqs = List.map convert_pair form.eqs in
    let neqs = List.map convert_pair form.neqs in
    let sspat_list =
      form.spat |> RMSet.to_list |>
      List.map (fun (name,i)-> printf "@[Retreiving %s. @]@?" name; (name,convert_tuple i)) in
    let splain_list =
      form.plain |> RMSet.to_list |>
      List.map (fun (name,i)->(name,convert_tuple i)) in
    let disjuncts = List.map (lift_pair form_to_syntax) form.disjuncts in
    {seqs= eqs;
      sneqs=neqs;
      sspat = SMSet.from_list sspat_list;
      splain = SMSet.from_list splain_list;
      sdisjuncts = disjuncts}
  in
  let sform = form_to_syntax form in
  {sform with
    seqs = sform.seqs @ eqs;
    sneqs = sform.sneqs @ neqs}

let make_syntactic ts_form =
  make_syntactic' Cterm.get_eqs Cterm.get_neqs_all ts_form

let make_syntactic_all ts_form =
  make_syntactic' Cterm.get_eqs_all Cterm.get_neqs_all ts_form

let make_syntactic_none ts_form =
  make_syntactic' (fun _ -> []) (fun _ -> []) ts_form


let match_and_remove
  remove (* should match terms be removed - true removes them, false leaves them *)
  ts
  term (*formula to match in *)
  pattern (*pattern to match *)
  combine (* combines results of continuations *)
  cont
=
  let rec mar_inner
	ts
	(term : RMSet.multiset)
	(cn (*current name*),cp (*current tuple pattern*))
	pattern(*remaining pattern*)
	count (*number of successive failures to match *)
	(cont : term_structure * RMSet.multiset -> 'a) : 'a =
      if RMSet.has_more term then
	(* actually do something *)
	let s,nterm = RMSet.remove term in
	if fst(s) = cn then
	  (* potential match *)
	  try
            let result =
              unifies ts cp (snd(s))
                (fun ts ->
                 (* If we are removing matched elements use nterm, otherwise revert to term *)
                  let nterm = if remove then nterm else term in
                  if SMSet.has_more pattern then
                    (* match next entry in the pattern*)
                    let ((nn,np), pattern) = SMSet.remove pattern in
                    (* If we are matching the same type of predicate still,
                       then must back the iterator up across the failed matches.  *)
                    let nterm = if nn=cn then (RMSet.back nterm count) else nterm in
                    let np,ts = make_tuple_pattern np ts in
                    mar_inner
                      ts
                      nterm
                      (nn, np)
                      pattern
                      0
                      cont
                  else
                    (* No pattern left, done *)
                    cont (ts,RMSet.restart nterm)
                ) in
            (try
              combine
                result
                (mar_inner ts (RMSet.next term) (cn, cp) pattern (count+1) cont)
            with Backtrack.No_match -> result)
          with Backtrack.No_match ->
	    (* Failed to match *)
	    mar_inner ts (RMSet.next term) (cn,cp) pattern (count+1) cont
	else if fst(s) < cn then
	  (* keeping searching for a new predicate, as current is too low. *)
	  mar_inner ts (RMSet.next term) (cn,cp) pattern 0 cont
	else
	  (* We have missed it, so no match *)
	  raise Backtrack.No_match
      else
	(* pattern left, but nothing to match against *)
	raise Backtrack.No_match
  in
    (* Check the pattern is non-empty *)
    if SMSet.has_more pattern then
      let (cn,cp),pattern = SMSet.remove pattern in
      let cp,ts = make_tuple_pattern cp ts in
      mar_inner ts term (cn,cp) pattern 0 cont
    else
      (* Empty pattern just call continuation *)
      cont (ts,term)


(* Invariant: [assumption] does not contain eqs or neqs, they are represented in [seq_ts] *)
type sequent =
   { matched : RMSet.multiset
   ; seq_ts : term_structure
   ; assumption : formula
   ; obligation : formula }

let check_sequent s =
  let rec check_empty form =
    assert (form.eqs = []);
    assert (form.neqs = []) in
(*
    let iter_pair f (a, b) = f a; f b in
    List.iter (iter_pair check_empty) form.disjuncts in
*)
  check_ts_formula {ts = s.seq_ts; form = s.assumption};
  check_ts_formula {ts = s.seq_ts; form = s.obligation};
  check_empty s.assumption

let pp_sequent ppf { matched; seq_ts; assumption; obligation } =
    let pp_term = pp_c seq_ts in
    let rmf = pp_star.separator (pp_rmset_element "" pp_term) ppf in
    ignore (RMSet.fold rmf true matched);
    fprintf ppf "@ | ";
    let first = pp_ts' pp_star ppf true seq_ts in
    ignore (pp_formula' pp_term pp_star ppf first assumption);
    fprintf ppf "@ |- ";
    pp_formula pp_term ppf obligation

let rec plain f =
  f.spat = RMSet.empty
    &&
  List.for_all (fun (x,y) -> plain x && plain y) f.disjuncts

let true_sequent (seq : sequent) : bool =
  (is_true seq.obligation)
    &&
  plain seq.assumption

let frame_sequent seq = seq.obligation = empty

(* TODO(rgrig): Remove this. *)
(* Stolen from Prover just for refactor *)
type sequent_rule = psequent * (psequent list list) * string * ((* without *) pform * pform) * (where list)


type pat_sequent =
  { assumption_same : syntactic_form
  ; assumption_diff : syntactic_form
  ; obligation_diff : syntactic_form }

let convert_sequent
  { ast_assumption_same = c; ast_assumption_diff = l; ast_obligation_diff = r }
=
  { assumption_same = convert_to_inner c
  ; assumption_diff = convert_to_inner l
  ; obligation_diff = convert_to_inner r }

type inner_sequent_rule =
    {
      conclusion : pat_sequent ;
      premises : pat_sequent list list;
      name : string;
      without_left : syntactic_form;
      without_right : syntactic_form;
      where : where list;
   }


let convert_rule (sr : sequent_rule) : inner_sequent_rule =
  match sr with
    conc,prems,name,(withoutl,withoutr),where ->
      {
       conclusion = convert_sequent conc;
       premises = List.map (List.map convert_sequent) prems;
       name = name;
       without_left = convert_to_inner withoutl;
       without_right = convert_to_inner withoutr;
       where = where;
     }

type logic = {
  seq_rules : inner_sequent_rule list;
  rw_rules : Psyntax.rewrite_rule list; (* RLP: No need to convert these it seems... *)
  consdecl : string list;
}
let empty_logic =
  { seq_rules = []
  ; rw_rules = []
  ; consdecl = [] }

let convert_logic l =
  { seq_rules = List.map convert_rule l.Psyntax.seq_rules
  ; rw_rules = l.Psyntax.rw_rules
  ; consdecl = l.Psyntax.consdecl }


(* Match in syntactic ones too *)
let rec match_foo op ts form seqs cont =
  match seqs with
    [] -> cont (ts,form)
  | (x,y)::seqs ->
      let x,ts = add_pattern x ts in
      let y,ts = add_pattern y ts in
      try
	op ts x y (fun ts -> match_foo op ts form seqs cont)
      with Backtrack.No_match ->
	let rec f ts frms frms2=
	  match frms with
	    (a,b)::frms ->
	      begin
		try
		  unifies ts x a
		    (fun ts -> unifies ts y b
			(fun ts -> match_foo op ts (frms@frms2) seqs cont) )
		with Backtrack.No_match -> try
		  unifies ts x b
		    (fun ts -> unifies ts y a
			(fun ts -> match_foo op ts (frms@frms2) seqs cont) )
		with Backtrack.No_match ->
		  f ts frms ((a,b)::frms2)
	      end
	  | [] -> raise Backtrack.No_match
	in
	f ts form []


let match_eqs ts eqs seqs cont =
  match_foo unify_patterns ts eqs seqs cont

let match_neqs ts neqs sneqs cont =
  match_foo unify_not_equal_pattern ts neqs sneqs cont



let rec match_form
  remove ts form pat
  combine
  (cont : term_structure * formula -> 'a)
  : 'a
=
  match_and_remove remove ts form.spat pat.sspat
      combine
  (fun (ts, spat) -> match_and_remove remove ts form.plain pat.splain
      combine
  (fun (ts, plain) -> match_eqs ts form.eqs pat.seqs
  (fun (ts, eqs) -> match_neqs ts form.neqs pat.sneqs
  (fun (ts, neqs) ->
    let form = { spat; plain; eqs; neqs; disjuncts = form.disjuncts } in
    match_disjunct remove combine pat.sdisjuncts (ts, form) cont))))

and new_match_form remove combine pat (ts, form) cont =
  let m0 (ts, form) cont =
    let cont (ts, spat) = cont (ts, { form with spat }) in
    match_and_remove remove ts form.spat pat.sspat combine cont in 
  let m1 (ts, form) cont =
    let cont (ts, plain) = cont (ts, { form with plain }) in
    match_and_remove remove ts form.plain pat.splain combine cont in
  let m2 (ts, form) cont =
    let cont (ts, eqs) = cont (ts, { form with eqs }) in
    match_eqs ts form.eqs pat.seqs cont in
  let m3 (ts, form) cont =
    let cont (ts, neqs) = cont (ts, { form with neqs }) in
    match_neqs ts form.neqs pat.sneqs cont in
  let m4 = match_disjunct remove combine pat.sdisjuncts in
  Backtrack.chain [m0; m1; m2; m3; m4] (ts, form) cont

and match_disjunct remove combine ds =
  let one_d (x, y) (ts, form) cont =
    let branch z = match_form remove ts form z combine cont in
    Backtrack.tryall branch [x; y] in
  Backtrack.chain (List.map one_d ds)

(* Takes a formula, and returns a pair of formula with one of the
   original disjuncts eliminated.*)
let split_disjunct form =
  match form.disjuncts with
    [] -> raise Backtrack.No_match
  | (x, y) :: disjuncts ->
      ( conjunction x { form with disjuncts },
        conjunction y { form with disjuncts } )

let internalise_qs (ts, form) =
  try
    let ts = add_eqs_list form.eqs ts in
    let ts = add_neqs_list form.neqs ts in
    (ts, {form with eqs = []; neqs = []})
  with Contradiction ->
    let form, ts = convert_sf false ts false_sform in
    (ts, form)

let apply_or_left seq =
  let a1,a2 = split_disjunct seq.assumption in
  let ts1, a1 = internalise_qs (seq.seq_ts, a1) in
  let ts2, a2 = internalise_qs (seq.seq_ts, a2) in
  [ [ { seq with seq_ts = ts1; assumption = a1 }
    ; { seq with seq_ts = ts2; assumption = a2 } ] ]

let apply_or_right seq : sequent list list =
  let o1,o2 = split_disjunct seq.obligation in
  [ [ { seq with obligation = o1 } ]
  ; [ { seq with obligation = o2 } ] ]


let get_frame seq =
  (*assert (frame_sequent seq);*) (* TODO: assertion broken by SMT, pick another *)
  mk_ts_form seq.seq_ts seq.assumption

let rec get_frames seqs frms =
  match seqs with
  | [] -> frms
  | seq::seqs ->  get_frames seqs ((get_frame seq)::frms)

let get_frames seqs =
  get_frames seqs []

let convert_with_eqs fresh pform =
  let sf = convert_to_inner pform in
  let ts = new_ts () in
  let form,ts = convert_sf fresh ts sf in
  mk_ts_form ts form

let convert fresh ts pform =
  convert_sf_without_eqs fresh ts (convert_to_inner pform)

let make_implies (heap : ts_formula) (pheap : pform) : sequent =
  let ts, assumption = break_ts_form heap in
  let obligation, seq_ts = convert false ts pheap in
  { seq_ts; assumption; obligation; matched = RMSet.empty }

let move_qs_to_formula { ts; form } =
  let raw_qs = Cterm.get_raw_qs ts in
  let form =
    { form with
      eqs = raw_qs.Cterm.raw_eqs @ form.eqs
    ; neqs = raw_qs.Cterm.raw_neqs @ form.neqs } in
  let ts = Cterm.forget_internal_qs ts in
  { ts; form }

let make_sequent ts_form1 ts_form2 =
  if safe then begin
    check_ts_formula ts_form1;
    check_ts_formula ts_form2
  end;
  let ts, assumption = break_ts_form ts_form1 in
  let ts_form2 = move_qs_to_formula ts_form2 in
  let subst, seq_ts = Cterm.conjoin ts ts_form2.ts in
  let assumption = substitute_in_formula subst assumption in
  let seq_ts, assumption = internalise_qs (seq_ts, assumption) in
  let obligation = ts_form2.form in
  { seq_ts; assumption; obligation; matched = RMSet.empty }

let ts_form_to_pform ts_form =
  convert_to_pform (make_syntactic_all ts_form)

let ts_form_to_pform_no_ts ts_form =
  convert_to_pform (make_syntactic_none ts_form)

let pform_to_ts_form pform =
  convert_with_eqs false pform

let purify_form f = { f with spat = RMSet.empty }
let purify_ts_form ts_form = { ts_form with form = purify_form ts_form.form }
