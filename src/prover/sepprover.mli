(********************************************************
   This file is part of coreStar
        src/prover/sepprover.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* I'm the main interface for src/prover. Read me. *)

open Corestar_std

type inner_form
type inner_logic

val inner_truth : inner_form
val inner_falsum : inner_form
val convert : Psyntax.form -> inner_form
val convert_logic : Psyntax.logic -> inner_logic
val convert_opt : Psyntax.form -> inner_form option (* deprecated *)
val conjoin : Psyntax.form -> inner_form -> inner_form (* deprecated *)
val conjoin_inner : inner_form -> inner_form -> inner_form
val kill_var : Psyntax.var -> inner_form -> inner_form
val abstract_val : inner_form -> inner_form
val join : inner_form -> inner_form -> inner_form
val meet : inner_form -> inner_form -> inner_form
val widening : inner_form -> inner_form -> inner_form
val join_over_numeric : inner_form -> inner_form -> inner_form * inner_form
val update_var_to : Psyntax.var -> Psyntax.term -> inner_form -> inner_form
val string_inner_form : inner_form pretty_printer

val implies : inner_logic -> inner_form -> inner_form -> bool
val inconsistent : inner_logic -> inner_form -> bool
val inconsistent_opt : inner_logic -> inner_form option -> bool
(*
val frame
  : inner_logic -> inner_form -> Psyntax.form -> inner_form list option
val frame_opt
  : inner_logic -> inner_form option -> Psyntax.form -> inner_form list option
  *)
val frame_inner
  : inner_logic -> inner_form -> inner_form -> inner_form list option
val abduct_inner
  : inner_logic -> inner_form -> inner_form
    -> (inner_form * inner_form) list option
val abs : inner_logic -> inner_form -> inner_form list
val abs_opt : inner_logic -> inner_form option -> inner_form list
val pprint_proof : Format.formatter -> unit
val pprint_counter_example : Format.formatter -> unit -> unit
val print_counter_example : unit -> unit
val string_of_proof : unit -> string
val get_counter_example : unit -> string
val implies_list : inner_form list -> Psyntax.form -> bool

val get_equals_pvar_free : Psyntax.var -> inner_form -> Psyntax.args list
  (** NOTE: [get_equals_pvar_free v f] is the empty list when [v] doesn't occur
  in [f]. *)

val get_pvars : inner_form -> Psyntax.var list
