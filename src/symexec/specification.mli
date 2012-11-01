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


val empty_inner_form : Sepprover.inner_form
val empty_inner_form_af : Sepprover.inner_form_af
val sub_spec : Psyntax.varmap -> Spec.ast_spec -> Spec.ast_spec
val jsr :
  Psyntax.logic ->
  Sepprover.inner_form_af ->
  Spec.ast_spec ->
  bool -> (Sepprover.inner_form_af list) option

(* These are not used by coreStar itself, but mey be useful to the frontend. *)
val spec_conjunction : Spec.ast_spec -> Spec.ast_spec -> Spec.ast_spec
val logical_vars_to_prog : Spec.ast_spec -> Spec.ast_spec
val refinement_extra :
  Psyntax.logic -> Spec.ast_spec -> Spec.ast_spec -> Psyntax.form -> bool
val refinement : Psyntax.logic -> Spec.ast_spec -> Spec.ast_spec -> bool
