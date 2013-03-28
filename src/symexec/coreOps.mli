(********************************************************
   This file is part of coreStar
        src/utils/coreOps.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(** {1 Operations on types defined in [Core].} *)

open Core
open Corestar_std


(** {2 Converters.} *)

val ast_to_inner_spec : ast_spec -> inner_spec
val ast_to_inner_core : ast_core -> inner_core


(** {2 Pretty printers.} *)

val pp_inner_spec : inner_spec pretty_printer
val pp_ast_core : ast_core pretty_printer
val pp_inner_core : inner_core pretty_printer
val pp_ast_question : ast_spec symb_question pretty_printer
