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

(** {1 Operations on types defined in [Core]} *)

open Core
open Corestar_std


(** {2 Pretty printers} *)

val pp_triple : triple pretty_printer
val pp_spec : spec pretty_printer
val pp_statement : statement pretty_printer
val pp_ast_procedure : ast_procedure pretty_printer
val pp_rules : rules pretty_printer
val pp_ast_question : ast_question pretty_printer


(** {2 Useful constants} *)
val empty_ast_question : Syntax.context -> ast_question

(** {2 Refinement on triples and specs.} *)
type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool
val refines_triple : Syntax.context -> triple refinement_check
val refines_spec : Syntax.context -> spec refinement_check

(** {2 Construct simple specs} *)
val mk_assume : Syntax.context -> Syntax.expr -> spec
val mk_assert : Syntax.expr -> spec
