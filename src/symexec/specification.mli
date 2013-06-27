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

(* TODO(rgrig): Move to [coreOps] or jStar. *)


val empty_inner_form : Sepprover.inner_form
val sub_triple : Psyntax.varmap -> Core.ast_triple -> Core.ast_triple
val logical_vars_to_prog : Core.ast_triple -> Core.ast_triple
