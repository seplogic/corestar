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



open Backtrack
open Clogic
open Cterm
open Debug
open Format
open Misc
open Psyntax
open Backtrack
open Smt
open Vars


let empty_sequent () =
  {
  matched = RMSet.empty;
  ts = Cterm.new_ts ();
  assumption = Clogic.empty;
  obligation = Clogic.empty;
  antiframe = Clogic.empty; 
}


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
  with No_match ->
    false



let sequent_join fresh (seq : sequent) (pseq : pat_sequent) : sequent option =
  try
    (* Construct new assumption *)
    let ass,ts =
      try
      convert_sf fresh  seq.ts pseq.assumption_diff
      with Contradiction ->
        fprintf !(Debug.proof_dump) 
          "Failed to add formula to lhs: %a@\n" 
          pp_syntactic_form pseq.assumption_diff;
      raise Contradiction
    in
    let ass = conjunction ass seq.assumption in
    
    (* Construct new antiframe *)
    let ant,ts = 
      try 
        convert_sf fresh ts pseq.antiframe_diff 
      with Contradiction -> 
        fprintf !(Debug.proof_dump) 
          "Failed to add formula to antiframe: %a@\n" 
          pp_syntactic_form pseq.antiframe_diff;
        raise Contradiction
    in 
    let ant = conjunction ant seq.antiframe in
    
    (* Construct new matched portion *)
    let sam,ts =
      try
        convert_sf fresh ts pseq.assumption_same
      with Contradiction ->
        fprintf !(Debug.proof_dump) 
          "Failed to add formula to matched: %a@\n" 
          pp_syntactic_form pseq.assumption_same;
        assert false in
    let sam = RMSet.union sam.spat seq.matched in
    
    (* Construct new obligation portion *)
    let obs,ts =
      try
        let obs,ts = convert_sf_without_eqs fresh ts pseq.obligation_diff in
        let obs = conjunction obs seq.obligation in
        obs,ts
      with Contradiction ->
        try
          convert_sf_without_eqs true ts false_sform
        with Contradiction -> assert false in

    Some {
      assumption = ass;
      obligation = obs;
      matched = sam;
      ts = ts;
      antiframe = ant; 
    }
  with Contradiction ->
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
	    Cterm.var_not_used_in seq.ts v sreps
	) varset
    | NotInTerm (Psyntax.Var varset, term) ->
	vs_for_all (
	  fun v ->
	    Cterm.var_not_used_in_term seq.ts v term
	) varset
    | PureGuard pf -> 
        if !Config.smt_run then 
          begin
            let sf = convert_to_inner pf in 
            let (f,ts) = convert_ground seq.ts sf in 
            if Config.smt_debug() then 
               Format.printf "[Calling SMT to discharge a pure guard]@\nguard:@\n%a@\nheap:@\n%a@\n" 
               pp_ts_formula (mk_ts_form ts f) pp_sequent seq;  
            Smt.finish_him ts seq.assumption f
          end
        else raise No_match
  ) wheres


(* TODO Doesn't use obligation equalities to help with match. *)
let apply_rule
     (sr : inner_sequent_rule)
     (seq : sequent)
     : sequent list list
     =
  (* Should reset any matching variables in the ts to avoid clashes. *)
  let ts = blank_pattern_vars seq.ts in
  (* Match obligation *)
  match_form true ts seq.obligation sr.conclusion.obligation_diff
    (@)
    (fun (ts_ob,ob) ->
  (* Match antiframe_diff *)
  match_form true ts seq.antiframe sr.conclusion.antiframe_diff
    (@)
    (fun (ts_ant,ant) -> 
  (* Match assumption_diff *)
  match_form true ts seq.assumption sr.conclusion.assumption_diff
    (@)
    (fun (ts_ass,ass) ->
	  (* match assumption_not removed *)
	  let ass_f = {ass with spat=RMSet.union ass.spat seq.matched} in
	  match_form true ts ass_f sr.conclusion.assumption_same
            (@)
	    (fun (ts,_) ->
	      if (not (is_sempty sr.without_left) && contains ts ass_f sr.without_left) then
		raise No_match
	      else if (not (is_sempty sr.without_right) && contains ts ob sr.without_right) then
		raise No_match
	      else if (not (check sr.where {seq with  (* TODO: do we want to use the old asm / ob here for the SMT guard? *)
					    ts = ts;
					    obligation = ob;
					    assumption = ass})) then
		  raise No_match
	      else begin
		fprintf !(Debug.proof_dump) "Match rule %s@\n" sr.name;
		let seq =
		  {seq with
		   ts = ts;
		   obligation = ob;
                   assumption = ass;
                   antiframe = ant; } in 
		List.map
		  (map_option
		     (sequent_join_fresh seq))
		  sr.premises
	      end
	    )
	    )
	)
    )


let rewrite_guard_check seq (ts,guard) =
  if contains ts seq.assumption (convert_to_inner guard.if_form) then
    let without = convert_to_inner guard.without_form in
    if not (is_sempty without) && contains ts seq.assumption without then
      false
    else
      check guard.rewrite_where seq
  else
    false


let simplify_sequent rm seq : sequent option
    =
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
      out_normalise seq.ts ass
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
      ts = ts;
      matched = f_spat;
      assumption = {ass with spat = a_spat};
      obligation =
      {obs with
	spat = o_spat;
	plain = o_plain;
	eqs = ob_eqs;
	neqs=ob_neqs
      }; 
      antiframe = seq.antiframe; (* FIXME: What should this do? *)
    } in
   (*  printf "After simplification : %a@\n" pp_sequent seq; *)
    Some seq
  with Failed ->
    let obs,ts = convert_sf_without_eqs true ts false_sform in
    Some {seq with
      ts = ts;
      assumption = ass;
      obligation = obs }

with Success -> None


let prover_counter_example : Clogic.sequent list ref = ref []

let pprint_counter_example ppf () = 
  fprintf ppf "Needed to prove:@   @[%a@]@\n@\n"
    (list_format "\nor" Clogic.pp_sequent)
    !prover_counter_example

let print_counter_example = pprint_counter_example std_formatter
  
let get_counter_example () =
  let out_buff = Buffer.create 1000 in
  let out_ft = Format.formatter_of_buffer out_buff in
  pprint_counter_example out_ft ();
  Format.pp_print_flush out_ft ();
  let r = Buffer.contents out_buff in
  Buffer.clear out_buff;
  r

let pprint_proof (f : formatter) : unit = 
  Format.pp_print_flush !proof_dump ();  
  fprintf f "%s" (Buffer.contents buffer_dump)

let string_of_proof () =
  Buffer.contents buffer_dump

exception Failed_eg of Clogic.sequent list


let rec apply_rule_list_once 
   (rules : sequent_rule list) 
   (seq : Clogic.sequent) 
   : Clogic.sequent list list
   =
  match rules with 
    [] -> raise No_match
  | rule::rules ->
      try 
      apply_rule (Clogic.convert_rule rule) seq
      with 
      | No_match -> apply_rule_list_once rules seq


let rec sequents_backtrack 
    f (seqss : Clogic.sequent list list) xs 
    : Clogic.sequent list =
  match seqss with 
    [] -> raise (Failed_eg xs)
  | seqs::seqss -> 
      try f seqs 
      with 
	Failed ->  
	  fprintf !proof_dump "Backtracking!@\n"; sequents_backtrack f seqss xs
      | Failed_eg x -> 
	  fprintf !proof_dump "Backtracking!@\n"; sequents_backtrack f seqss (x @ xs)

let apply_rule_list 
    (logic : logic) 
    (sequents : Clogic.sequent list) 
    (must_finish : Clogic.sequent -> bool) 
    (may_finish : Clogic.sequent -> bool) 
    : Clogic.sequent list 
    =
(* Clear pretty print buffer *)
  Buffer.clear buffer_dump;
(*  let rules,rwm,ep = logic in *)
  let n = 0 in
  if log log_prove then
    (List.iter (fun seq -> fprintf !proof_dump "Goal@ %a@\n@\n" Clogic.pp_sequent seq) sequents;
     fprintf !proof_dump "Start time :%f @\n" (Sys.time ()));
  let rec apply_rule_list_inner sequents n : Clogic.sequent list = 
    let search seqss : Clogic.sequent list = 
      sequents_backtrack 
	(fun seqs->apply_rule_list_inner seqs (n+1)) seqss [] in
    let sequents = map_option (simplify_sequent logic.rw_rules) sequents in 
  (* Apply rules lots *)
    List.flatten 
      (List.map 
	 (fun seq ->
	   fprintf !proof_dump "%s>@[%a@]@\n@." (String.make n '-') Clogic.pp_sequent  seq;
	   if must_finish seq then 
	     [seq]
	   else
	   try 
	     search (apply_rule_list_once logic.seq_rules seq)
	   with No_match -> 
	   try 
		 if may_finish seq then 
		   [seq]
		 else 
		   search ([Clogic.apply_or_left seq])
	       with No_match -> 
		 try 
		   search (Clogic.apply_or_right seq)
		 with No_match -> 
                 try 
	             let ts' = Smt.ask_the_audience seq.ts seq.assumption in
	             search [[ {seq with ts = ts'} ]]
                   with 
                   | Assm_Contradiction -> []
                   | No_match -> raise (Failed_eg [seq])
	 ) sequents 
      )
  in let res = apply_rule_list_inner sequents n in 
  if log log_prove then 
    fprintf !proof_dump "@\nEnd time :%f@ " (Sys.time ());
  res

let check_imp (logic : logic) (seq : sequent) : bool = 
    try 
      let ts = List.fold_right Cterm.add_constructor logic.consdecl seq.ts in 
      let seq = {seq with ts = ts} in 
      ignore (apply_rule_list logic [seq] Smt.true_sequent_smt Smt.true_sequent_smt); true
    with  
      Failed -> false
    | Failed_eg x -> prover_counter_example := x ; false

let check_frm (logic : logic) (seq : sequent) : Clogic.F.ts_formula list option =
  try
    let ts = List.fold_right Cterm.add_constructor logic.consdecl seq.ts in 
    let seq = {seq with ts = ts} in
    let leaves = apply_rule_list logic [seq] (fun _ -> false) Smt.frame_sequent_smt in 
    Some (Clogic.get_frames leaves)
  with 
    Failed -> fprintf !proof_dump "Frame failed\n"; None 
  | Failed_eg x -> fprintf !proof_dump "Frame failed\n"; prover_counter_example := x; None 


let check_abduct logic seq : Clogic.AF.ts_formula list option = 
  try 
    let leaves = apply_rule_list logic [seq] (fun _ -> false) Clogic.abductive_sequent in 
    (* the lists of frames and antiframes have equal lengths *)
    Some (Clogic.get_frames_antiframes leaves)
  with 
    Failed -> Format.fprintf !proof_dump "Abduction failed\n"; None
  | Failed_eg x -> Format.fprintf !proof_dump "Abduction failed\n"; prover_counter_example := x; None 


let check_implication_frame_pform logic heap pheap  =  
  check_frm logic (Clogic.make_implies heap pheap)


let check_implication_pform 
    (logic : logic) 
    (heap : F.ts_formula) 
    (pheap : pform) : bool =  
  check_imp logic (Clogic.make_implies heap pheap)


let check_abduction_pform logic heap pheap = 
  check_abduct logic (Clogic.make_implies heap pheap)


(* abstract P by applying frame inference to P => emp *)
(* result should be collection of abstracted frames F implying P *)
let abs 
    (logic : logic) 
    (ts_form : F.ts_formula)
    : F.ts_formula list  = 
  match check_frm logic  (Clogic.make_implies ts_form []) with 
    Some r -> r
  | None -> 
      (* Abstraction cannot fail *)
      assert false

let check_implication_syntactic logic pform pform2 = 
  let seq = make_sequent (Clogic.convert_sequent ([],pform,pform2,mkEmpty)) in
  match seq with 
    None -> true (* Found contradiction immediately *)
  | Some seq -> 
      check_imp logic seq

let check_implication_frame_syntactic logic pform pform2 = 
  let seq = make_sequent (Clogic.convert_sequent ([],pform,pform2,mkEmpty)) in
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
