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
  { Core.pre = p1; post = q1; modifies = m1 }
  { Core.pre = p2; post = q2; modifies = m2 }
=
  let v = PS.Arg_var (Vars.freshe ()) in
  let one = PS.mkEQ (v, PS.Arg_string "case*one") in
  let two = PS.mkEQ (v, PS.Arg_string "case*two") in
  let ( && ) = PS.mkStar and ( || ) = curry PS.mkOr in
  { Core.pre = (one && p1) || (two && p2)
  ; post = (one && q1) || (two && q2)
  ; modifies = Misc.remove_duplicates compare (m1 @ m2) }


(***************************************
   Refinement type stuff
 ***************************************)


let sub_triple sub { Core.pre; post; modifies } =
  let var2var v = match PS.find v sub with
    | PS.Arg_var w -> w
    | _ -> failwith "INTERNAL: pre of Specification.sub_triple doesn't hold" in
  { Core.pre = PS.subst_pform sub pre
  ; post = PS.subst_pform sub post
  ; modifies = List.map var2var modifies }

let ev_triple { Core.pre; post } = PS.ev_form_acc post (PS.ev_form pre)

let logical_vars_to_prog triple =
  let ev = PS.ev_form triple.Core.pre in
  let sub = PS.subst_kill_vars_to_fresh_prog ev in
  sub_triple sub triple

let refinement_inner logic triple1 triple2 =
  P.implies logic triple2.Core.pre triple1.Core.pre &&
  P.implies logic triple1.Core.post triple2.Core.post

let refinement_inner_extra logic triple1 triple2 extra =
  P.implies logic (Sepprover.conjoin_inner triple2.Core.pre extra) triple1.Core.pre &&
  P.implies logic triple1.Core.post triple2.Core.post
