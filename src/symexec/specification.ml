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
module VS = Psyntax.VarSet

let empty_inner_form =
  match P.convert_opt PS.mkEmpty with
    None -> assert false;
  | Some emp -> emp

let join_triples
  { Core.pre = p1; post = q1 } { Core.pre = p2; post = q2 }
=
  let v = PS.Arg_var (Vars.freshe ()) in
  let one = PS.mkEQ (v, PS.Arg_string "case*one") in
  let two = PS.mkEQ (v, PS.Arg_string "case*two") in
  let ( && ) = PS.mkStar and ( || ) = curry PS.mkOr in
  { Core.pre = (one && p1) || (two && p2)
  ; post = (one && q1) || (two && q2) }


(***************************************
   Refinement type stuff
 ***************************************)


let sub_triple sub { Core.pre; post} =
  { Core.pre = PS.subst_pform sub pre; post = PS.subst_pform sub post }

let ev_triple { Core.pre; post } = PS.ev_form_acc post (PS.ev_form pre)

(*
let simple_jsr logic state triple =
  let ev = ev_triple triple in
  let sub = PS.subst_kill_vars_to_fresh_exist ev in
  let triple = sub_triple sub triple in
  let frames = P.frame logic state triple.Core.pre in
  let add_post fs =
    let star_post = P.conjoin triple.Core.post in
    let star_post f = try Some (star_post f) with PS.Contradiction -> None in
    let r = map_option star_post fs in
    List.map (VS.fold P.kill_var ev) r in
  option_map add_post frames
*)

let logical_vars_to_prog triple =
  let ev = PS.ev_form triple.Core.pre in
  let sub = PS.subst_kill_vars_to_fresh_prog ev in
  sub_triple sub triple


(* Notation: triplei is {Pi}..{Qi}; extra is E

Checks that
  if    P2 * E |- P1 * F
  then  Q1 * F |- Q2
for all F found by the prover.

TODO(rgrig): Doesn't seem sound to me, because of "found by the prover". *)
let refinement_extra logic triple1 triple2 extra =
  let triple2 = logical_vars_to_prog triple2 in
  let stronger q = true (* XXX P.implies logic q triple2.Core.post *) in
  let all_stronger qs = List.for_all stronger qs in
  let run_from state = true in
(* XXX    option false all_stronger (simple_jsr logic state triple1) in *)
  run_from (P.convert (PS.mkStar extra triple2.Core.pre))

(*  triple2 ==> triple1
That is
   triple2
   -----
     :
   -----
   triple1
*)
let refinement logic triple1 triple2 =
    refinement_extra logic triple1 triple2 []


