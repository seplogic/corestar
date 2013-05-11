(********************************************************
   This file is part of coreStar
        src/symbexe/specification.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* TODO(rgrig): Move to [coreOps] and jStar. *)


val empty_inner_form : Sepprover.inner_form
val sub_triple : Psyntax.varmap -> Core.ast_triple -> Core.ast_triple
(*
val simple_jsr : Psyntax.logic ->
  Sepprover.inner_form -> Core.ast_triple -> Sepprover.inner_form list option
*)

(* These are not used by coreStar itself, but may be useful to the frontend. *)
val join_triples : Core.ast_triple -> Core.ast_triple -> Core.ast_triple

val logical_vars_to_prog : Core.ast_triple -> Core.ast_triple
val refinement_extra :
  Psyntax.logic -> Core.ast_triple -> Core.ast_triple -> Psyntax.form -> bool
val refinement : Psyntax.logic -> Core.ast_triple -> Core.ast_triple -> bool
