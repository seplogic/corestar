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

module P = Sepprover
module PS = Psyntax
module S = Spec
module VS = Psyntax.VarSet

(* XXX type ts_excep_post = inner_form ClassMap.t *)

let empty_inner_form =
  match P.convert PS.mkEmpty with
    None -> assert false;
  | Some emp -> emp

let empty_inner_form_af =
  P.lift_inner_form empty_inner_form

let spec_conjunction { Spec.pre = p1; post = q1 } { Spec.pre = p2; post = q2} =
  let v = PS.Arg_var (Vars.freshe ()) in
  let one = PS.mkEQ (v, PS.Arg_string "case*one") in
  let two = PS.mkEQ (v, PS.Arg_string "case*two") in
  let ( && ) = PS.mkStar and ( || ) = curry PS.mkOr in
  { Spec.pre = (one && p1) || (two && p2)
  ; post = (one && q1) || (two && q2) }


(***************************************
   Refinement type stuff
 ***************************************)


let sub_spec sub { S.pre; post} =
  { S.pre = PS.subst_pform sub pre; post = PS.subst_pform sub post }

let ev_spec { S.pre; post } = PS.ev_form_acc post (PS.ev_form pre)

(* if pre_antiframe = None then perform jsr, otherwise perform jsr with abduction *)
let jsr logic state spec abduct =
  let ev = ev_spec spec in
  let subst = PS.subst_kill_vars_to_fresh_exist ev in
  let spec = sub_spec subst spec in
  let pre_form = P.inner_form_af_to_form state in
  let frame_antiframe_list =
    if abduct then
      P.abduction_opt logic (Some pre_form) spec.S.pre
    else
      option_map (List.map P.lift_inner_form) (P.frame logic pre_form spec.S.pre)
  in
  let faf_state = P.inner_form_af_to_af state in
  let add_post fafs =
    let star_post s = P.conjoin_af s spec.S.post faf_state in
    let star_post_opt s =
      try Some (star_post s) with PS.Contradiction -> None in
    let r = Misc.map_option star_post_opt fafs in
    List.map (VS.fold P.kill_var_af ev) r in
  option_map add_post frame_antiframe_list

(* TODO(rgrig): This should replace [jsr] after the "_af" stuff is removed. *)
let simple_jsr logic state spec =
  let ev = ev_spec spec in
  let sub = PS.subst_kill_vars_to_fresh_exist ev in
  let spec = sub_spec sub spec in
  let frames = P.frame logic state spec.S.pre in
  let add_post fs =
    let star_post = P.conjoin spec.S.post in
    let star_post f = try Some (star_post f) with PS.Contradiction -> None in
    let r = Misc.map_option star_post fs in
    List.map (VS.fold P.kill_var ev) r in
  option_map add_post frames

let logical_vars_to_prog spec =
  let ev = PS.ev_form spec.S.pre in
  let sub = PS.subst_kill_vars_to_fresh_prog ev in
  sub_spec sub spec


(* Notation: speci is {Pi}..{Qi}; extra is E

Checks that
  if    P2 * E |- P1 * F
  then  Q1 * F |- Q2
for all F found by the prover.

TODO(rgrig): Doesn't seem sound to me, because of "found by the prover". *)
let refinement_extra logic spec1 spec2 extra =
  let spec2 = logical_vars_to_prog spec2 in
  let stronger q = P.implies logic q spec2.S.post in
  let all_stronger qs = List.for_all stronger qs in
  let run_from state =
    maybe false all_stronger (simple_jsr logic state spec1) in
  maybe true run_from (P.convert (PS.mkStar extra spec2.S.pre))

(*  spec2 ==> spec1
That is
   spec2
   -----
     :
   -----
   spec1
*)
let refinement logic spec1 spec2 =
    refinement_extra logic spec1 spec2 []


