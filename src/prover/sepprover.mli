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

open Psyntax

type inner_form

val inner_truth : inner_form
val inner_falsum : inner_form
val convert : form -> inner_form option
val conjoin : form -> inner_form -> inner_form
val conjoin_inner : inner_form -> inner_form -> inner_form
val kill_var : var -> inner_form -> inner_form
val abstract_val : inner_form -> inner_form
val join : inner_form -> inner_form -> inner_form
val meet : inner_form -> inner_form -> inner_form
val widening : inner_form -> inner_form -> inner_form
val join_over_numeric : inner_form -> inner_form -> inner_form * inner_form
val update_var_to : var -> term -> inner_form -> inner_form
val string_inner_form : Format.formatter -> inner_form -> unit

val implies : logic -> inner_form -> form -> bool
val implies_opt : logic -> inner_form option -> form -> bool
val inconsistent : logic -> inner_form -> bool
val inconsistent_opt : logic -> inner_form option -> bool
val frame : logic -> inner_form -> form -> inner_form list option
val frame_opt : logic -> inner_form option -> form -> inner_form list option
val frame_inner : logic -> inner_form -> inner_form -> inner_form list option
val abs : logic -> inner_form -> inner_form list
val abs_opt : logic -> inner_form option -> inner_form list
val pprint_proof : Format.formatter -> unit
val pprint_counter_example : Format.formatter -> unit -> unit
val print_counter_example : unit -> unit
val string_of_proof : unit -> string
val get_counter_example : unit -> string
val implies_list : inner_form list -> form -> bool

(* TODO(rgrig): Remove these. It's wrong to share equalities. *)
type inner_form_af
val lift_inner_form : inner_form -> inner_form_af
val inner_form_af_to_form : inner_form_af -> inner_form
val inner_form_af_to_af : inner_form_af -> inner_form
val conjoin_af : inner_form_af -> form -> inner_form -> inner_form_af
val conjoin_inner_af : inner_form_af -> inner_form -> inner_form -> inner_form_af
val combine : inner_form -> inner_form -> inner_form_af
val kill_var_af : var -> inner_form_af -> inner_form_af
val update_var_to_af : var -> term -> inner_form_af -> inner_form_af
val string_inner_form_af : Format.formatter -> inner_form_af -> unit
val abduction_opt : logic -> (inner_form option) -> form -> inner_form_af list option

