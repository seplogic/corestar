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


(** {2 Converters} *)

val ast_to_inner_triple : ast_triple -> inner_triple
val ast_to_inner_spec : ast_spec -> inner_spec
val ast_to_inner_core : ast_core -> inner_core

(** {2 Pretty printers} *)

val pp_ast_triple : ast_triple pretty_printer
val pp_inner_triple : inner_triple pretty_printer
val pp_ast_spec : ast_spec pretty_printer
val pp_inner_spec : inner_spec pretty_printer
val pp_ast_core : ast_core pretty_printer
val pp_inner_core : inner_core pretty_printer
val pp_ast_proc : ast_procedure pretty_printer
val pp_ast_question : ast_question pretty_printer


(** {2 Special variable names} *)
val name_ret_v1 : string
val ret_v1 : Vars.var
val return_var : int -> Vars.var
val parameter : int -> string
val parameter_var : int -> Vars.var

val global_prefix : string

val is_parameter : Vars.var -> bool
val is_return : Vars.var -> bool
val is_global : Vars.var -> bool

(** {2 Useful constants} *)
val empty_question : 'b -> ('a, 'b) question

(** {2 Refinement on triples and specs.} *)
type 'a refinement_check = Sepprover.inner_logic -> 'a -> 'a -> bool
val refines_triple : inner_triple refinement_check
val refines_spec : inner_spec refinement_check

(** {2 Construct simple specs} *)
val mk_assume : Sepprover.inner_form -> inner_spec
val mk_assert : 'a -> 'a triple spec
