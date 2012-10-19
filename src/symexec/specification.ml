(********************************************************
   This file is part of coreStar
        src/symbexe/specification.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)



(** Support functions for symbolic execution and misc conversion facilities. *)

open Corestar_std
open Psyntax
open Sepprover
open Spec

type ts_excep_post = inner_form ClassMap.t 

let empty_inner_form = 
  match convert mkEmpty with
    None -> assert false;
  | Some emp -> emp

let empty_inner_form_af =
  lift_inner_form empty_inner_form
  
let conjunction_excep excep_post f1 =
  ClassMap.map (fun post -> Psyntax.pconjunction post f1) excep_post

let conjunction_excep_convert excep_post f1 =
  ClassMap.map (fun post -> Sepprover.conjoin post f1) excep_post

let combine_maps empty fold add find combine_values m1 m2 =
  let combine_add k v m =
    try add k (combine_values v (find k m)) m
    with Not_found -> add k v m in
  fold combine_add m1 m2

let disjunction_excep = 
  combine_maps ClassMap.empty ClassMap.fold ClassMap.add ClassMap.find (curry mkOr)

let spec_conjunction spec1 spec2 =
  let var = Arg_var(Vars.freshe()) in
  let zero = Arg_string("**first**") in
  let one = Arg_string("**second**") in
  let eq = mkEQ(var,zero) in 
  let neq = mkEQ(var,one) in       
  match spec1,spec2 with 
    {pre=pre1; post=post1; excep=excep1},
    {pre=pre2; post=post2; excep=excep2} ->
      {pre= Psyntax.mkOr ((Psyntax.pconjunction pre1 eq),(Psyntax.pconjunction pre2 neq));
       post= Psyntax.mkOr ((Psyntax.pconjunction post1 eq),(Psyntax.pconjunction post2 neq));
       excep = disjunction_excep (conjunction_excep excep1 eq) (conjunction_excep excep2 neq)}



(***************************************
   Refinement type stuff 
 ***************************************)


(* 
   { e1 : f1} , ... , {en :  fn}   (excep1)  
   ===>
   { e1' : f1', ... , {em' : fm'}  (excep2)
iff
forall ei :fi. exists ej' : fj'.  ei=ej' /\ fi==>fj'
*)
exception Check_fails

let implication_excep logic excep1 excep2 = 
  try 
    ClassMap.iter (
    fun exname form -> 
      if Sepprover.implies logic form (ClassMap.find exname excep2) 
      then ()
      else raise Check_fails
   ) excep1; true
  with check_fails -> false

let sub_spec  sub spec =
  match spec with 
    {pre=pre; post=post; excep=excep} ->
      {pre=subst_pform sub pre;
       post=subst_pform sub post;
       excep=ClassMap.map (subst_pform sub) excep}
      
let ev_spec spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre in 
      let ev = ev_form_acc spec_post ev in 
      let ev = ClassMap.fold (fun key ex vs -> ev_form_acc ex vs) spec_excep ev in 
      ev

let ev_spec_pre spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre in 
      ev


(* if pre_antiframe = None then perform jsr, otherwise perform jsr with abduction *)
let jsr logic (pre : inner_form_af) (spec : spec) (abduct : bool) : inner_form_af list option  = 
  let ev = ev_spec spec in 
  let subst = subst_kill_vars_to_fresh_exist ev in 
  let spec = sub_spec subst spec in
  let pre_form = inner_form_af_to_form pre in
  match spec with
    {pre=spec_pre; post=spec_post; excep=spec_excep} ->
    let frame_antiframe_list = 
      if abduct then
        Sepprover.abduction_opt logic (Some pre_form) spec_pre
      else
        (let frame_list = Sepprover.frame logic pre_form spec_pre in
        match frame_list with
          None -> None
        | Some frame_list -> 
          Some (List.map (fun inner_form -> lift_inner_form inner_form) frame_list))
    in
    match frame_antiframe_list with
      None -> None
    | Some frame_antiframe_list ->
      let res = Misc.map_option 
        (fun frame_antiframe ->
          try Some (Sepprover.conjoin_af frame_antiframe spec_post (inner_form_af_to_af pre))
          with Contradiction -> None) 
        frame_antiframe_list in 
      let res = List.map (fun frame_antiframe -> 
        vs_fold (fun e ts_form -> kill_var_af e ts_form) ev frame_antiframe) res in 
      Some res


(* TODO: need exceptions in jsr? *)
let jsr_excep logic (pre : inner_form) (spec : spec) : (inner_form  list * ts_excep_post list) option = 
  let ev = ev_spec spec in 
  let subst = subst_kill_vars_to_fresh_exist ev in 
  let spec = sub_spec subst spec in 
  match spec with
    {pre=spec_pre; post=spec_post; excep=spec_excep} -> 
      let frame_list = Sepprover.frame logic pre spec_pre in 
      match frame_list with
        None -> None
      |	Some frame_list -> 
        let res = Misc.map_option 
          (fun post -> (*Prover.tidy_one*) 
            try Some (Sepprover.conjoin spec_post post) with Contradiction -> None) 
        frame_list in 
        let excep_res = List.map (conjunction_excep_convert spec_excep) frame_list in 
        let res = List.map (fun ts -> vs_fold (fun e ts -> kill_var e ts) ev ts) res in 
        Some (res,excep_res)


let logical_vars_to_prog spec2 = 
  let ev = ev_spec_pre spec2 in 
  let sub = subst_kill_vars_to_fresh_prog ev in 
  sub_spec sub spec2 

(*  spec2={P}{Q} =[extra]=> spec1  
 
   {P*extra}{Q} ===> spec1
*)
let refinement_extra (logic : logic) (spec1 : spec) (spec2 : spec) (extra : pform): bool =
  let spec2 = logical_vars_to_prog spec2 in 
  match spec2 with
    {pre=pre; post=post; excep=excep} ->
      match (Sepprover.convert (extra&&&pre)) with 
	None -> true
      |	Some form -> 
	  match jsr_excep logic form spec1 with 
	    None -> false
	  | Some (newposts, newexcep_posts) ->
	      let res = List.for_all (fun newpost -> Sepprover.implies logic newpost post) newposts in 
	      let res2 = List.for_all (fun newexcep_post -> implication_excep logic newexcep_post excep) newexcep_posts in 
	      (res&&res2)


(*  spec2 ==> spec1 
That is
   spec2
   -----
     :
   ----- 
   spec1  
*)
let refinement (logic : logic) (spec1 : spec) (spec2 : spec) : bool =
    refinement_extra logic spec1 spec2 [] 



