(********************************************************
   This file is part of coreStar
        src/symexec_ast/spec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Data structures used to represent specifications. *)

open Corestar_std

module ClassMap = StringMap

type excep_post = Psyntax.pform ClassMap.t

(* XXX: have a variant for inner_form *)
type spec =
    { pre : Psyntax.form
    ; post : Psyntax.form
    ; excep : excep_post }

