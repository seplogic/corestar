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


(** {2 Special variable names} *)
val name_ret_v1 : Expression.var
val return : int -> Expression.var
val parameter : int -> Expression.var

val global_prefix : string

val is_parameter : string -> bool
val is_return : string -> bool
val is_global : string -> bool

(** {2 Useful constants} *)
val empty_ast_question : ast_question

(** {2 Refinement on triples and specs.} *)
type 'a refinement_check = Calculus.t -> 'a -> 'a -> bool
val refines_triple : triple refinement_check
val refines_spec : spec refinement_check

(** {2 Construct simple specs} *)
val mk_assume : Expression.t -> spec
val mk_assert : Expression.t -> spec
