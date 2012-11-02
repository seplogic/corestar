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

module P = Sepprover

type 'a spec = { pre : 'a; post : 'a }
type ast_spec = Psyntax.form spec
type inner_spec = P.inner_form spec

let form_to_inner_form x = match P.convert x with
    | None -> P.inner_falsum
    | Some x -> x

let ast_to_inner_spec { pre; post } =
  let c = form_to_inner_form in { pre = c pre; post = c post }
