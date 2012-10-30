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

type excep_post = Psyntax.form ClassMap.t

(* XXX: have a variant for inner_form *)
(* XXX: remove excep; that's in jStar, but not coreStar *)
type spec =
    { pre : Psyntax.form
    ; post : Psyntax.form
    ; excep : excep_post }

