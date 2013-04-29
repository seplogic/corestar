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
  let reps = (RMSet.map_to_list form.spat snd) @ reps in
  let reps = (RMSet.map_to_list form.plain snd)  @ reps in
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.eqs in
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.neqs in
  let reps = List.fold_left (fun acc (a,b) -> form_reps a (form_reps b acc)) reps form.disjuncts in
  reps

let rec sequent_reps sequent reps =
  let reps = (RMSet.map_to_list sequent.matched snd) @ reps in
  let reps = form_reps sequent.assumption reps in
  let reps = form_reps sequent.obligation reps in
  reps

let rec sequent_ass_reps sequent reps =
  let reps = (RMSet.map_to_list sequent.matched snd) @ reps in
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
      with Contradiction ->
        fprintf !(Debug.proof_dump)
          "Failed to add formula to lhs: %a@\n"
          pp_syntactic_form pseq.assumption_diff;
      raise Contradiction
    in
    let assumption = conjunction ass seq.assumption in

    (* Construct new matched portion *)
    let sam,ts =
      try
        convert_sf fresh ts pseq.assumption_same
      with Contradiction ->
        fprintf !(Debug.proof_dump)
          "Failed to add formula to matched: %a@\n"
          pp_syntactic_form pseq.assumption_same;
        assert false in
    let matched = RMSet.union sam.spat seq.matched in

    (* Construct new obligation portion *)
    let obligation, seq_ts =
      try
        let obs,ts = convert_sf_without_eqs fresh ts pseq.obligation_diff in
        let obs = conjunction obs seq.obligation in
        obs, ts
      with Contradiction ->
        try
          convert_sf_without_eqs true ts false_sform
        with Contradiction -> assert false in
    Some { assumption; obligation; matched; seq_ts }
  end with Contradiction ->
    fprintf !(Debug.proof_dump) "Contradiction detected!!@\n";
    None


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
  fprintf !(Debug.proof_dump) "@[Match rule %s@]@\n" sr.name;
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
  (*  printf "Before simplification : %a@\n" pp_sequent seq ;*)
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
    with Contradiction ->
      fprintf !(Debug.proof_dump)"Success: %a@\n" pp_sequent seq;
      raise Success
  in
  try
    let obs,_ =
      try Clogic.normalise ts obs
      with Contradiction ->
        raise Failed in
    let ob_eqs = obs.eqs in
    let rec duts ts ob_eqs new_ob_eqs =
      match ob_eqs with
        [] -> ts,  new_ob_eqs
      | (a,b)::ob_eqs ->
          let ts,obeq = determined_exists ts (sequent_ass_reps seq []) a b in
          duts ts ob_eqs (obeq @ new_ob_eqs) in
    let ts, ob_eqs = try duts ts ob_eqs [] with Contradiction -> raise Failed in
    let ob_neqs = obs.neqs in
    let ts = try Cterm.rewrite ts rm (rewrite_guard_check seq) with Contradiction -> raise Success in
    let ob_eqs,ts_ob = try remove equal make_equal ts ob_eqs with Contradiction -> raise Failed in
    let ob_neqs,ts_ob = try remove not_equal make_not_equal ts_ob ob_neqs with Contradiction -> raise Failed in
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
   (*  printf "After simplification : %a@\n" pp_sequent seq; *)
    Some seq
  with Failed ->
    let obs,ts = convert_sf_without_eqs true ts false_sform in
    Some {seq with
      seq_ts = ts;
      assumption = ass;
      obligation = obs }
with Success -> None


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

let pprint_proof (f : formatter) : unit =
  pp_print_flush !proof_dump ();
  fprintf f "%s" (Buffer.contents buffer_dump)

let string_of_proof () =
  Buffer.contents buffer_dump

(*
exception Failed_eg of Clogic.sequent list
*)

(* A goal with penalty [<= Backtrack.min_penalty] is discharged.  A goal with with score
[> Backtrack.max_penalty] needs a proof.  Anything in-between is kind of acceptable as a
leaf, but we should keep looking for something better. *)
let rec solve rules penalty n goal =
  let leaf = ([goal], penalty goal) in
  if n = 0 then leaf else begin
    let process_rule r =
      let subgoals = r goal in
      Backtrack.combine_list (solve rules penalty (n-1)) ([], 0) subgoals in
    Backtrack.choose_list process_rule leaf rules
  end

let min_depth = 2
let max_depth = 10

let solve_idfs rules penalty goal =
  Backtrack.choose (flip (solve rules penalty) goal) ((<) max_depth) succ Backtrack.fail min_depth

(* If a rule does not match, it should raise Backtrack.No_match. *)
let search_rules rules =
  let try_rule r = List.flatten @@ (apply_rule (Clogic.convert_rule r)) in (* RLP: Check flatten is OK *)
  let try_rules = List.map try_rule rules in
  let try_or_left = Clogic.apply_or_left in
  let try_or_right = List.flatten @@ Clogic.apply_or_right in
  let try_smt seq =
    try
      let ts = Smt.ask_the_audience seq.seq_ts seq.assumption in
      [ {seq with seq_ts = ts} ]
    with Assm_Contradiction -> [] in
  try_rules @ (try_or_left :: try_or_right :: [try_smt])

let frame_penalty g =
  if Smt.frame_sequent_smt g then 0 else Backtrack.max_penalty

let check_frm (logic : logic) (seq : sequent) : Clogic.ts_formula list option =
  try
    let ts = List.fold_right Cterm.add_constructor logic.consdecl seq.seq_ts in
    let seq = {seq with seq_ts = ts} in
    let rules = search_rules logic.seq_rules in
    let leaves, penalty = solve_idfs rules frame_penalty seq in
    if penalty >= Backtrack.max_penalty then raise Backtrack.No_match else
    Some (Clogic.get_frames leaves)
  with Backtrack.No_match -> fprintf !proof_dump "Frame failed\n"; None

let check_imp logic sequent = is_some (check_frm logic sequent)

(* Many choices possible here... *)
let abduction_penalty g = List.length g.assumption.disjuncts

(* RLP: this code typechecks, but not at all sure it does the right thing... *)
let abduct logic hypothesis conclusion = (* failwith "TODO: Prover.abduct" *)
  try
    let seq = Clogic.make_implies_inner hypothesis conclusion in
    (* RLP: What does this bit do? *)
    let ts = List.fold_right Cterm.add_constructor logic.consdecl seq.seq_ts in
    let seq = {seq with seq_ts = ts} in
    let rules = search_rules logic.seq_rules in
    let leaves, penalty = solve_idfs rules abduction_penalty seq in
    if penalty >= Backtrack.max_penalty then raise Backtrack.No_match else
    let frameanti seq =
      Clogic.mk_ts_form seq.seq_ts seq.assumption,
      Clogic.mk_ts_form seq.seq_ts seq.obligation in
    Some (List.map frameanti leaves)
  with Backtrack.No_match -> fprintf !proof_dump "Abduction failed\n"; None


let check_implication_frame_pform logic heap pheap  =
  check_frm logic (Clogic.make_implies heap pheap)


let check_implication_pform
    (logic : logic)
    (heap : ts_formula)
    (pheap : pform) : bool =
  check_imp logic (Clogic.make_implies heap pheap)


(* abstract P by applying frame inference to P => emp *)
(* result should be collection of abstracted frames F implying P *)
let abs
    (logic : logic)
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
  let seq = Clogic.make_implies_inner ts_form1 ts_form2 in
  check_imp logic seq

let check_frame logic ts_form1 ts_form2 =
  let seq = Clogic.make_implies_inner ts_form1 ts_form2 in
  check_frm logic seq


(* let check_inconsistency logic ts_form   = assert false *)
(*  check_implication_inner logic ts heap1 ([],[],[False]) *)
(* TODO: Check whether this makes sense *)
let check_inconsistency logic ts_form =
  check_implication logic ts_form (Clogic.convert_with_eqs false mkFalse)


let check_implies_list fl1 pf =
  List.for_all
    (fun f1 ->
      check_implication_pform empty_logic f1 pf
    ) fl1
