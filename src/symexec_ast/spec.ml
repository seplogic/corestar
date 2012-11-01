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

type 'a spec = { pre : 'a; post : 'a }
type ast_spec = Psyntax.form spec
type inner_spec = Sepprover.inner_form spec
