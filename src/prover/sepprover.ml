(********************************************************
   This file is part of coreStar
        src/prover/sepprover.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(*F#
namespace Microsoft.Research.Vcc2
F#*)

open Debug
open Psyntax


    (*****************************************
       Internal formula operations
     *****************************************)

    type inner_form = Clogic.ts_formula

    let inner_truth =
      Clogic.mk_ts_form (Cterm.new_ts ()) Clogic.truth

    let inner_falsum =
      let form,ts = Clogic.convert_sf false (Cterm.new_ts ()) Clogic.false_sform in
      Clogic.mk_ts_form ts form

    let convert : form -> inner_form option
      = fun form ->
        try Some (Clogic.convert_with_eqs false form)
        with Contradiction -> None

    let conjoin : form -> inner_form -> inner_form
      = fun form inner_form -> Clogic.conjoin false inner_form (Clogic.convert_to_inner form)

    let conjoin_inner : inner_form -> inner_form -> inner_form
      = fun if1 if2 -> Clogic.conjoin false if1 (Clogic.make_syntactic if2)

    let kill_var : var -> inner_form -> inner_form
      = fun v inner_form ->
        Clogic.kill_var inner_form v

    let abstract_val : inner_form -> inner_form
      = fun inner_form ->
        let pform = Clogic.ts_form_to_pform inner_form in
        let abs_pform = Plugin_manager.abstract_val pform in
        let abs_inner_form = Clogic.pform_to_ts_form abs_pform in
        abs_inner_form

    let join : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.join pf1 pf2 with
        | [] -> Format.printf "No plugin with join loaded!\n"; inner_truth
        | pf::_ -> Clogic.pform_to_ts_form pf

    let meet : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.meet pf1 pf2 with
        | [] -> Format.printf "No plugin with meet loaded!\n"; inner_falsum
        | pf::_ -> Clogic.pform_to_ts_form pf

    let widening : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.widening pf1 pf2 with
        | [] -> Format.printf "No plugin with widening loaded!\n"; inner_truth
        | pf::_ -> Clogic.pform_to_ts_form pf

    let join_over_numeric : inner_form -> inner_form -> inner_form * inner_form
      = fun if1 if2 ->
        let split_numerical (pform : pform) : pform * pform =
          List.partition (fun pf_at -> is_numerical_pform_at pf_at) pform in
        let num_pf1,rest_pf1 = split_numerical (Clogic.ts_form_to_pform if1) in
        let num_pf2,rest_pf2 = split_numerical (Clogic.ts_form_to_pform if2) in
        let join_ts_form =
          match Plugin_manager.join num_pf1 num_pf2 with
          | [] -> Format.printf "No plugin with join loaded!\n"; inner_truth
          | pf::_ -> Clogic.pform_to_ts_form pf
        in
        (conjoin rest_pf1 join_ts_form, conjoin rest_pf2 join_ts_form)

    let update_var_to : var -> term -> inner_form -> inner_form
      = fun v e f -> Clogic.update_var_to f v e

    let string_inner_form : Format.formatter -> inner_form -> unit =
      Clogic.pp_ts_formula

    (******************************************
       Entailment operations
     ******************************************)

    let implies : logic -> inner_form -> form -> bool
      = fun logic inner_form1 form2 -> Prover.check_implication_pform logic inner_form1 form2

    let implies_opt : logic -> inner_form option -> form -> bool
      = fun logic inner_form1 form2 ->
	match inner_form1 with
	  None -> true
	| Some inner_form1 -> Prover.check_implication_pform logic inner_form1 form2

    let inconsistent : logic -> inner_form -> bool
      = fun logic inner_form1 -> Prover.check_inconsistency logic inner_form1

    let inconsistent_opt : logic -> inner_form option -> bool
      = fun logic inner_form1 ->
	match inner_form1 with
	  None -> true
	| Some inner_form1 -> Prover.check_inconsistency logic inner_form1

    let frame : logic -> inner_form -> form -> inner_form list option
      = fun logic inner_form1 form2 ->
	Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_opt : logic -> inner_form option -> form -> inner_form list option
	= fun logic inner_form1 form2 ->
	  match inner_form1 with
	    None -> Some []
	  | Some inner_form1 ->
	      Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_inner (l : logic) (i1 : inner_form) (i2 : inner_form) : inner_form list option =
      Prover.check_frame l i1 i2

    let abduct_inner = Prover.abduct

    let abs : logic -> inner_form -> inner_form list
      = Prover.abs

    let abs_opt : logic -> inner_form option -> inner_form list
      = fun l form -> match form with None -> [] | Some form -> Prover.abs l form

    let implies_list : inner_form list -> form -> bool
      = Prover.check_implies_list

    let get_equals_pvar_free : var -> inner_form -> Psyntax.args list
      = fun v form ->
        Cterm.get_equals_pvar_free form.Clogic.ts v


   let pprint_proof = Prover.pprint_proof
   let pprint_counter_example = Prover.pprint_counter_example
   let print_counter_example = Prover.print_counter_example
   let get_counter_example = Prover.get_counter_example
   let string_of_proof = Prover.string_of_proof
