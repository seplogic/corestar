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

let empty_inner_form = P.convert PS.mkEmpty

let sub_triple sub { Core.pre; post; modifies } =
  let var2var v = match PS.find v sub with
    | PS.Arg_var w -> w
    | _ -> failwith "INTERNAL: pre of Specification.sub_triple doesn't hold" in
  { Core.pre = PS.subst_pform sub pre
  ; post = PS.subst_pform sub post
  ; modifies = option_map (List.map var2var) modifies }

let ev_triple { Core.pre; post } = PS.ev_form_acc post (PS.ev_form pre)

let logical_vars_to_prog triple =
  let ev = PS.ev_form triple.Core.pre in
  let sub = PS.subst_kill_vars_to_fresh_prog ev in
  sub_triple sub triple

