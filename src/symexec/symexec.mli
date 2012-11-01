(********************************************************
   This file is part of coreStar
        src/symbexe/symexec.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val file : string ref
val verify :
  string ->
  Cfg_core.cfg_node list ->
  Spec.ast_spec -> Psyntax.logic -> Psyntax.logic -> bool
val verify_ensures :
  string ->
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  (Psyntax.pform -> Psyntax.form) ->
  Sepprover.inner_form list list -> Psyntax.logic -> Psyntax.logic -> unit
val bi_abduct :
  string ->
  Cfg_core.cfg_node list ->
  Spec.ast_spec ->
  Psyntax.logic ->
  Psyntax.logic ->
  Psyntax.logic ->
  (Sepprover.inner_form * Sepprover.inner_form) list

(* TODO: This is only used by translatejimple in jstar, so perhaps it should not be here. *)
val get_frame :
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  Psyntax.logic -> Psyntax.logic -> Sepprover.inner_form list


(* TODO(rgrig): Should these be here? Only jStar uses them. *)
val set_group : bool -> unit
val pp_dotty_transition_system : unit -> unit
