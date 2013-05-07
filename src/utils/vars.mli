(********************************************************
   This file is part of coreStar
        src/utils/vars.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Variables are of orthogonally ditinguished in fresh/concrete and e/a/p
(existential/universal/program).  Concrete vars are hashconsed, by name. *)

open Corestar_std

type var

val is_avar : var -> bool
val is_evar : var -> bool
val is_pvar : var -> bool

val fresh : (int -> 'a -> 'b) -> 'a -> 'b
val freshp_str : string -> var
val freshe_str : string -> var
val fresha_str : string -> var
val freshp : unit -> var
val freshe : unit -> var
val fresha : unit -> var

val is_fresh : var -> bool

module StrVarHash : Hashtbl.S with type key = string

val concretep_str : string -> var
val concretee_str : string -> var
val concretea_str : string -> var
val freshen : var -> var
val freshen_exists : var -> var

val pp_var : var pretty_printer
val string_var : var -> string
