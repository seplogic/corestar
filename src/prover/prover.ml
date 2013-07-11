(********************************************************
   This file is part of coreStar
        src/prover/prover.ml
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
open Clogic
open Cterm
open Misc
open Psyntax
open Smt
open Vars

module PS = Psyntax

let empty_sequent () =
  { matched = RMSet.empty
  ; seq_ts = Cterm.new_ts ()
  ; assumption = Clogic.empty
  ; obligation = Clogic.empty }

let rec out_normalise ts form =
  let form,ts = Clogic.normalise ts form in
  if form.eqs <> [] || form.neqs <> [] then
    begin
      let ts = add_eqs_list form.eqs ts in
      let ts = add_neqs_list form.neqs ts in
      let form,ts = out_normalise ts {form with eqs = []; neqs = []} in
      form,ts
    end
  else
    form,ts


let rec form_reps form reps =
  let reps = (List.map snd (RMSet.to_list form.spat)) @ reps in
  let reps = (List.map snd (RMSet.to_list form.plain))  @ reps in
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.eqs in
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.neqs in
  let reps = List.fold_left (fun acc (a,b) -> form_reps a (form_reps b acc)) reps form.disjuncts in
  reps

let rec sequent_reps sequent reps =
  let reps = (List.map snd (RMSet.to_list sequent.matched)) @ reps in
  let reps = form_reps sequent.assumption reps in
  let reps = form_reps sequent.obligation reps in
  reps

let rec sequent_ass_reps sequent reps =
  let reps = (List.map snd (RMSet.to_list sequent.matched)) @ reps in
  let reps = form_reps sequent.assumption reps in
  reps


let contains ts form pat : bool  =
  try
    match_form true ts form pat (||) (fun (ts2,_) -> if Cterm.ts_eq ts ts2 (*This checks that no unification has occured in the contains*) then true else  raise Backtrack.No_match)
  with Backtrack.No_match ->
    false



let sequent_join fresh (seq : sequent) (pseq : pat_sequent) : sequent option =
  try begin
    (* Construct new assumption *)
    let ass,ts =
      try
      convert_sf fresh  seq.seq_ts pseq.assumption_diff
      with Contradiction -> begin
        if log log_prove then
          fprintf logf "Failed to add formula to lhs: %a@\n"
          pp_syntactic_form pseq.assumption_diff;
        raise Contradiction
      end
    in
    let assumption = conjunction ass seq.assumption in

    (* Construct new matched portion *)
    let sam,ts =
      try
        convert_sf fresh ts pseq.assumption_same
      with Contradiction -> begin
        if log log_prove then
          fprintf logf "Failed to add formula to matched: %a@\n"
          pp_syntactic_form pseq.assumption_same;
        assert false
      end in
    let matched = RMSet.union sam.spat seq.matched in

    (* Construct new obligation portion *)
    let obligation, seq_ts =
      try
        let obs,ts = convert_sf_without_eqs fresh ts pseq.obligation_diff in
        let obs = conjunction obs seq.obligation in
        obs, ts
      with Contradiction ->
        try
          printf "Replacing contradiction with False@\n@?"; (* DBG *)
          convert_sf_without_eqs true ts false_sform
        with Contradiction -> assert false in
    Some { assumption; obligation; matched; seq_ts }
  end with Contradiction -> begin
    if log log_prove then
      fprintf logf "Contradiction detected!!@\n";
    None
  end


let sequent_join_fresh = sequent_join true
let sequent_join = sequent_join false


let make_sequent (pseq : pat_sequent) : sequent option =
  sequent_join (empty_sequent ()) pseq


let check wheres seq : bool  =
  let sreps = sequent_reps seq [] in
  List.for_all
    (
  function
    | NotInContext (Psyntax.Var varset) ->
        vs_for_all (
          fun v ->
            Cterm.var_not_used_in seq.seq_ts v sreps
        ) varset
    | NotInTerm (Psyntax.Var varset, term) ->
        vs_for_all (
          fun v ->
            Cterm.var_not_used_in_term seq.seq_ts v term
        ) varset
    | PureGuard pf ->
        if !Config.smt_run then
          begin
            let sf = convert_to_inner pf in
            let (f,ts) = convert_ground seq.seq_ts sf in
            if Config.smt_debug () then begin
              printf "@[[Calling SMT to discharge a pure guard]";
              printf "@\n@[<2>guard:@\n%a@]" pp_ts_formula (mk_ts_form ts f);
              printf "@\n@[<2>heap:@\n%a@]" pp_sequent seq;
              printf "@]@\n"
            end;
            Smt.finish_him ts seq.assumption f
          end
        else raise Backtrack.No_match
  ) wheres


(* TODO Doesn't use obligation equalities to help with match. *)
let apply_rule sr seq =
  let seq_ts = blank_pattern_vars seq.seq_ts in (* to avoid clashes *)
  match_form true seq_ts seq.obligation sr.conclusion.obligation_diff
    (@)
    (fun (seq_ts, obligation) ->
  match_form true seq_ts seq.assumption sr.conclusion.assumption_diff
    (@)
    (fun (seq_ts, assumption) ->
      (* match assumption_not removed *)
      let ass_f = { assumption with spat = RMSet.union assumption.spat seq.matched } in
  match_form true seq_ts ass_f sr.conclusion.assumption_same
    (@)
    (fun (seq_ts, _) ->

  (* Main processing *)
  let seq = { matched = seq.matched; seq_ts; obligation; assumption } in
  let ok =
    is_sempty sr.without_left
    && contains seq_ts ass_f sr.without_left
    && is_sempty sr.without_right
    && contains seq_ts obligation sr.without_right
    && is_sempty sr.without_right
    && contains seq_ts obligation sr.without_right
    && check sr.where seq in (* TODO: do we want to use the old asm / ob here for the SMT guard? *)
  if not ok then raise Backtrack.No_match;
  if log log_prove then fprintf logf "@[Match rule %s@]@\n" sr.name;
  List.map (map_option (sequent_join_fresh seq)) sr.premises)))

let rewrite_guard_check seq (ts,guard) =
  if contains ts seq.assumption (convert_to_inner guard.if_form) then
    let without = convert_to_inner guard.without_form in
    if not (is_sempty without) && contains ts seq.assumption without then
      false
    else
      check guard.rewrite_where seq
  else
    false


let simplify_sequent rm seq =
try
  printf "Using %d rw-rules to simplify %a.@\n@?" (List.length rm) pp_sequent seq;
  (* Try to prove each equality and inequality using ts.
   Note we assume ones we can prove to prove the rest.*)
  let remove test update =
    let rec remove_rec rem_eqs ts eqs =
      match eqs with
        [] -> rem_eqs,ts
      | (x,y)::eqs ->
          if test ts x y then
            remove_rec rem_eqs ts eqs
          else
            begin
              let ts = update ts x y in
              remove_rec ((x,y)::rem_eqs) ts eqs
            end
    in remove_rec []
  in
  let ass = seq.assumption in
  let obs = seq.obligation in
  let ass,ts =
    try
      out_normalise seq.seq_ts ass
    with Contradiction -> begin
      if log log_prove then
        fprintf logf "Success: %a@\n" pp_sequent seq;
      raise Success
    end
  in
  try
    let obs,_ =
      try Clogic.normalise ts obs
      with Contradiction ->
        (printf "XXX Failed 1@\n@?";
        raise Failed) in
    let ob_eqs = obs.eqs in
    let rec duts ts ob_eqs new_ob_eqs =
      match ob_eqs with
        [] -> ts, new_ob_eqs
      | (a,b)::ob_eqs ->
          let ts,obeq = determined_exists ts (sequent_ass_reps seq []) a b in
          duts ts ob_eqs (obeq @ new_ob_eqs) in
    let ts, ob_eqs =
      try duts ts ob_eqs []
      with Contradiction ->
        (printf "XXX Failed 2@\n@?";
        raise Failed) in
    let ob_neqs = obs.neqs in
    let ts = try Cterm.rewrite ts rm (rewrite_guard_check seq) with Contradiction -> raise Success in
    let ob_eqs,ts_ob =
      try remove equal make_equal ts ob_eqs
      with Contradiction ->
        (printf "XXX Failed 3@\n@?";
        raise Failed) in
    let ob_neqs,ts_ob =
      try remove not_equal make_not_equal ts_ob ob_neqs
      with Contradiction ->
        (printf "XXX Failed 4@\n@?";
        raise Failed) in
  (* Assuming obligations equalities and inequalities,
     and try to match same terms on each side *)
    let a_spat = ass.spat in
    let o_spat = obs.spat in
  (* Look for all the o_spat terms in a_spat,
     shared terms will be f_spat
  *)
    let (f_spat,o_spat,a_spat) = intersect_with_ts ts_ob true o_spat a_spat in
    let f_spat = RMSet.union seq.matched f_spat in
    let a_plain = ass.plain in
    let o_plain = obs.plain in
    let (_,o_plain,_) = intersect_with_ts ts_ob false o_plain a_plain in
    let ts = try Cterm.rewrite ts rm (rewrite_guard_check seq) with Contradiction -> raise Success in
    let seq = {
      seq_ts = ts;
      matched = f_spat;
      assumption = {ass with spat = a_spat};
      obligation =
      {obs with
        spat = o_spat;
        plain = o_plain;
        eqs = ob_eqs;
        neqs=ob_neqs
      }
    } in
    (*printf "After simplification : %a@\n" pp_sequent seq;*)
    Some seq
  with Failed ->
    printf "XXX YEP, Failed@\n@?";
    let obs,ts = convert_sf_without_eqs true ts false_sform in
    Some {seq with
      seq_ts = ts;
      assumption = ass;
      obligation = obs }
  with Success -> None

let simplify { Clogic.seq_ts; assumption; obligation; matched } =
  try
    let process_q mk_q ts (a, b) =
      if Cterm.is_evar ts a || Cterm.is_evar ts b
      then (printf "XXX addq(%a,%a)@\n@?"
        (Cterm.pp_c ts) a (Cterm.pp_c ts) b; mk_q ts a b) else ts in
    let seq_ts =
      List.fold_left (process_q Cterm.make_equal) seq_ts obligation.Clogic.eqs in
    let seq_ts =
      List.fold_left (process_q Cterm.make_not_equal) seq_ts obligation.Clogic.neqs in
    let unknown_eq (a, b) = not (Cterm.equal seq_ts a b) in
    let unknown_neq (a, b) = not (Cterm.not_equal seq_ts a b) in
    let eqs = List.filter unknown_eq obligation.Clogic.eqs in
    let neqs = List.filter unknown_neq obligation.Clogic.neqs in
    let obligation = { obligation with Clogic.eqs; neqs } in
    [[{ seq_ts; assumption; obligation; matched }]]
  with Contradiction -> (printf "XXX got contradiction@\n@?"; [])

let prover_counter_example : Clogic.sequent list ref = ref []

let pprint_counter_example ppf () =
  fprintf ppf "Needed to prove:@   @[%a@]@\n@\n"
    (pp_list_sep " or " Clogic.pp_sequent)
    !prover_counter_example

let print_counter_example = pprint_counter_example std_formatter

let get_counter_example () =
  let out_buff = Buffer.create 1000 in
  let out_ft = formatter_of_buffer out_buff in
  pprint_counter_example out_ft ();
  pp_print_flush out_ft ();
  let r = Buffer.contents out_buff in
  Buffer.clear out_buff;
  r

(*
exception Failed_eg of Clogic.sequent list
*)

type named_rule =
  { rule_name : string (* For debug *)
  ; rule_apply : Clogic.sequent -> Clogic.sequent list list }

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with with score
[> Backtrack.max_penalty] needs a proof.  Anything in-between is kind of acceptable as a
leaf, but we should keep looking for something better. *)
let rec solve rules penalty n goal =
  if safe then Clogic.check_sequent goal;
  if log log_prove then
    fprintf logf "@,@[<v 2>prove goal@ @[%a@]" Clogic.pp_sequent goal;
  let leaf = ([goal], penalty goal) in
  let result =
    if n = 0 then leaf else begin
      let process_rule r =
        let subgoals = r.rule_apply goal in
        if log log_prove then
          fprintf logf "@\n@[Applied rule %s@\n@]@?" r.rule_name;
	if safe then List.iter (List.iter Clogic.check_sequent) subgoals;
        subgoals in
      let solve_subgoal = solve rules penalty (n-1) in
      let solve_all_subgoals = Backtrack.combine_list solve_subgoal ([], 0) in
      let choose_alternative = Backtrack.choose_list solve_all_subgoals leaf in
      let choose_rule =
        Backtrack.choose_list (choose_alternative @@ process_rule) in
      choose_rule leaf rules
    end in
  if log log_prove then fprintf logf "@]@?";
  result


let min_depth = 2
let max_depth = 3

let solve_idfs ?min_depth:(min_depth=min_depth) ?max_depth:(max_depth=max_depth) rules penalty goal =
  if log log_prove then fprintf logf "@,@[<v 2>start idfs proving";
  if safe then Clogic.check_sequent goal;
  let solve = flip (solve rules penalty) goal in
  let fail = ([], Backtrack.max_penalty) in
  let give_up i = i > max_depth in
  let r = Backtrack.choose solve give_up succ fail min_depth in
  if log log_prove then fprintf logf "@]@,@?";
  r

(* If a rule does not match, it should raise Backtrack.No_match. *)
let search_rules logic =
  let try_identity = 
    { rule_name = "identity"
    ; rule_apply = fun s ->
      if s.obligation = s.assumption then [[]] else raise Backtrack.No_match } in
(*  let try_simplify =  XXX this does something complicated that fails sometimes
    { rule_name = "simplify_by_rewrite"
    ; rule_apply = fun s ->
      match simplify_sequent logic.Clogic.rw_rules s with
      | None -> []
      | Some simp_s -> [[simp_s]] } in *)
  let try_simplify =
    { rule_name = "simplify eqs/neqs"
    ; rule_apply = simplify } in
  let try_rule r =
    { rule_name = r.Clogic.name
    ; rule_apply = apply_rule r } in
  let try_rules = try_identity :: try_simplify :: List.map try_rule logic.Clogic.seq_rules in
  let try_or_left =
    { rule_name = "Or_left"
    ; rule_apply = Clogic.apply_or_left } in
  let try_or_right =
    { rule_name = "Or_right"
    ; rule_apply = Clogic.apply_or_right } in
  let try_smt =
    { rule_name = "SMT"
    ; rule_apply = fun seq ->
      try
	let ts = Smt.ask_the_audience seq.seq_ts seq.assumption in
        [[ {seq with seq_ts = ts} ]]
      with Assm_Contradiction -> [[]] } in
  let native_rules = try_or_left :: try_or_right :: List.rev try_rules in
  let all_rules =
    if !Config.smt_run then try_smt :: native_rules else native_rules in
  List.rev all_rules
  (* NOTE: try user provided rules first; the others explode the search space *)

let frame_penalty g =
  let p = if !Config.smt_run then Smt.frame_sequent_smt else Clogic.frame_sequent in
  if p g then 0 else Backtrack.max_penalty

let check_frm ?min_depth:(min_depth=min_depth) ?max_depth:(max_depth=max_depth) logic (seq : sequent) : Clogic.ts_formula list option =
  try
    let ts = List.fold_right Cterm.add_constructor logic.Clogic.consdecl seq.seq_ts in
    if safe then Clogic.check_sequent seq;
    let seq = {seq with seq_ts = ts} in
    if safe then Clogic.check_sequent seq;
    let rules = search_rules logic in
    let leaves, penalty = solve_idfs ~min_depth:min_depth ~max_depth:max_depth rules frame_penalty seq in
    if penalty >= Backtrack.max_penalty then raise Backtrack.No_match else
      (if log log_prove then fprintf logf "@[Frames found: %d@]@,@?" (List.length leaves);
       Some (Clogic.get_frames leaves))
  with Backtrack.No_match -> if log log_prove then fprintf logf "@[Frame failed@]@,@?"; None

let check_imp ?min_depth:(min_depth=min_depth) ?max_depth:(max_depth=max_depth) logic sequent =
  is_some (check_frm ~min_depth:min_depth ~max_depth:max_depth logic sequent)

(* Two on each side then we should look for more *)
let abduction_penalty g = 
  let count spat = Clogic.RMSet.fold (fun n _ -> succ n) 0 spat in
  6 * (count g.assumption.spat + count g.obligation.spat)

(* RLP: this code typechecks, but not at all sure it does the right thing... *)
let abduct logic hypothesis conclusion = (* failwith "TODO: Prover.abduct" *)
  try
    let seq = Clogic.make_sequent hypothesis conclusion in
    (* RLP: What does this bit do? *)
    let ts = List.fold_right Cterm.add_constructor logic.Clogic.consdecl seq.seq_ts in
    let seq = {seq with seq_ts = ts} in
    let rules = search_rules logic in
    let leaves, penalty = solve_idfs rules abduction_penalty seq in
    if penalty >= Backtrack.max_penalty then raise Backtrack.No_match else
      let antiframe_frame seq =
	let ts = Cterm.forget_internal_qs seq.seq_ts in
	(Clogic.mk_ts_form ts seq.obligation,
	 Clogic.mk_ts_form seq.seq_ts seq.assumption) in
      let result = List.map antiframe_frame leaves in
      if log log_prove then (
        let pp_fa f (aa, af) = fprintf f "@,@[(A: %a,@ F: %a)@]"
          Clogic.pp_ts_formula aa Clogic.pp_ts_formula af in
        fprintf logf "@[<2>Abduction suceeded, found %d antiframe/frame pair(s):%a@]@,@?" (List.length result) (pp_list pp_fa) result
      );
      Some result
  with Backtrack.No_match -> if log log_prove then fprintf logf "@[Abduction failed@]@,@?"; None


let check_implication_frame_pform logic heap pheap  =
  check_frm logic (Clogic.make_implies heap pheap)


let check_implication_pform
    logic
    (heap : ts_formula)
    (pheap : pform) : bool =
  check_imp logic (Clogic.make_implies heap pheap)


(* abstract P by applying frame inference to P => emp *)
(* result should be collection of abstracted frames F implying P *)
let abs
    logic
    (ts_form : ts_formula)
    : ts_formula list  =
  match check_frm logic  (Clogic.make_implies ts_form []) with
    Some r -> r
  | None ->
      (* Abstraction cannot fail *)
      assert false

let check_implication_syntactic logic pform pform2 =
  let seq = PS.mk_psequent [] pform pform2 in
  let seq = make_sequent (Clogic.convert_sequent seq) in
  match seq with
    None -> true (* Found contradiction immediately *)
  | Some seq ->
      check_imp logic seq

let check_implication_frame_syntactic logic pform pform2 =
  let seq = PS.mk_psequent [] pform pform2 in
  let seq = make_sequent (Clogic.convert_sequent seq) in
  match seq with
    None -> Some [] (* Found contradiction immediately *)
  | Some seq ->
      check_frm logic seq


let check_implication logic ts_form1 ts_form2 =
  let seq = Clogic.make_sequent ts_form1 ts_form2 in
  if safe then Clogic.check_sequent seq;
  check_imp logic seq

let check_frame logic ts_form1 ts_form2 =
  let seq = Clogic.make_sequent ts_form1 ts_form2 in
  if safe then Clogic.check_sequent seq;
  check_frm logic seq


(* let check_inconsistency logic ts_form   = assert false *)
(*  check_implication_inner logic ts heap1 ([],[],[False]) *)
(* TODO: Check whether this makes sense *)
let check_inconsistency logic ts_form =
  let seq = Clogic.make_sequent ts_form (Clogic.convert_with_eqs false mkFalse) in
  if safe then Clogic.check_sequent seq;
  check_imp ~min_depth:2 ~max_depth:2 logic seq


let check_implies_list fl1 pf =
  List.for_all
    (fun f1 ->
      check_implication_pform Clogic.empty_logic f1 pf
    ) fl1
