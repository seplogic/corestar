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
val empty_ast_question : ast_question

(** {2 Refinement on triples and specs.} *)
type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool
val refines_triple : triple refinement_check
val refines_spec : spec refinement_check
val specialize_spec : Z3.Expr.expr list -> Z3.Expr.expr list -> Z3.Expr.expr list -> Z3.Expr.expr list -> spec -> spec

(** {2 Construct simple specs} *)
val mk_assume : Z3.Expr.expr -> spec
val mk_assert : Z3.Expr.expr -> spec

(** {2 Checks} *)
val is_well_formed : ast_question -> bool
