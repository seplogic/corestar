(********************************************************
   This file is part of coreStar
        src/prover/abs.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Syntactic abstraction *)
(* TODO: Possibly incorrect treatment of disjunctions *)
(* TODO: Rewrite to operate on pform directly *)

open Cterm
open Clogic
open Psyntax
open Plugin


(* Finds existentials in the spatial part *)
let rec find_ev_sp syn =
  if syn.sdisjuncts = [] then
    SMSet.fold_to_list syn.sspat (fun t vs -> 
      vs_union (ev_args_list (snd t) vs_empty) vs) vs_empty
  else begin
    List.fold_left (fun vs (s1, s2) -> 
      vs_union (vs_union (find_ev_sp s1) (find_ev_sp s2)) vs
    ) vs_empty syn.sdisjuncts   
  end


(* Finds existentials in equalities and inequalities *)
let rec find_ev_eq_neq syn vset =
  let get_evs a1 a2 =
    if (vs_is_empty (vs_inter vset (ev_args a1 vs_empty)) <> true ||
      vs_is_empty (vs_inter vset (ev_args a2 vs_empty)) <> true) then
      vs_union vset (vs_union (ev_args a1 vs_empty) (ev_args a2 vs_empty))
    else
      vset
  in
  if syn.sdisjuncts = [] then
    let evs_eqs = List.fold_left (fun vs (a1, a2) -> vs_union vs (get_evs a1 a2)) vs_empty syn.seqs in
    let evs_neqs = List.fold_left (fun vs (a1, a2) -> vs_union vs (get_evs a1 a2)) vs_empty syn.sneqs in
    vs_union evs_eqs evs_neqs
  else begin
    List.fold_left (fun vs (s1, s2) -> 
      vs_union (vs_union (find_ev_eq_neq s1 vset) (find_ev_eq_neq s2 vset)) vs
    ) vs_empty syn.sdisjuncts   
  end


(* Heuristic abstraction on syntactic form that eliminates existentials which are not in the spatial part *)
let kill_unused_existentials syn_form =
  (* iterates until the set of existentials becomes saturated *)
  let rec saturate_ev syn evars =
    let new_evars = find_ev_eq_neq syn evars in
    if (vs_is_empty (vs_diff new_evars evars)) then new_evars
    else saturate_ev syn new_evars
  in
  let rec saturate_ev_cnt syn evars cnt =
    if cnt = 0 then evars
    else saturate_ev_cnt syn (find_ev_eq_neq syn evars) (cnt-1)
  in  
  (*let ev_sp = saturate_ev_cnt syn_form (find_ev_sp syn_form) 2 in*)
  let ev_sp = saturate_ev syn_form (find_ev_sp syn_form) in
  let rec elim_evars syn =
    (* ignore terms with heads from forbidden_heads *)
    let forbidden_heads = ["Ast"] in
    let rec is_not_forbidden arg =
      match arg with
      | Arg_var v -> true
      | Arg_string s -> true
      | Arg_op (name, args) -> 
        ((List.mem name forbidden_heads) <> true) && 
        (List.for_all (fun arg -> is_not_forbidden arg) args)
      | _ -> assert false
    in
    (* condition for killing a term *)
    let can_kill vs =
      (vs_is_empty vs <> true) &&  (* the set of free variables must be non empty *)
      (vs_is_empty (vs_inter ev_sp vs)) &&  (* the intersection with existentials in spatials must be empty *)
      (vs_for_all Vars.is_evar vs) (* in there should be only existential vars *)
    in
    (* filters terms in a multiset *)
    let rec filter_args_mset ms : SMSet.multiset =
      if SMSet.has_more ms then begin
        if can_kill (fv_args_list (snd (SMSet.peek ms)) vs_empty) &&
          ((List.mem (fst (SMSet.peek ms)) forbidden_heads) <> true) then
          filter_args_mset (snd (SMSet.remove ms))
        else
          filter_args_mset (SMSet.next ms)
      end
      else SMSet.restart ms
    in
    (* filters terms in a list of pairs *)
    let filter_args_pls xs =
      List.filter (fun (a1, a2) ->
        (can_kill (vs_union (fv_args a1 vs_empty) (fv_args a2 vs_empty)) <> true) &&
        (is_not_forbidden a1) && (is_not_forbidden a2)
      ) xs
    in
    if syn.sdisjuncts = [] then
      let plain = filter_args_mset syn.splain in
      let eqs = filter_args_pls syn.seqs in
      let neqs = filter_args_pls syn.sneqs in
      { sspat = syn.sspat;
        splain = plain;
        sdisjuncts = syn.sdisjuncts;
        seqs = eqs;
        sneqs = neqs }
    else
      let disjuncts = 
        List.map (fun (s1, s2) -> (elim_evars s1, elim_evars s2)) syn.sdisjuncts
      in
      { sspat = syn.sspat;
        splain = syn.splain;
        sdisjuncts = disjuncts;
        seqs = syn.seqs;
        sneqs = syn.sneqs }
  in
  if Config.symb_debug() then
    Format.printf "\nBefore syntactic abstraction: %a@\n"  pp_syntactic_form syn_form;
  let abs_syn_form = elim_evars syn_form in
  if Config.symb_debug() then
    Format.printf "After syntactic abstraction: %a@\n"  pp_syntactic_form abs_syn_form;
  abs_syn_form


let syn_abs pform =
  let syn_form = convert_to_inner pform in
  let abs_syn_form = kill_unused_existentials syn_form in
  convert_to_pform abs_syn_form


let my_abs_int = {
  abstract_val = Some (ref syn_abs);
  join = None;
  meet = None;
  widening = None;
}

(* Plugin registration *)
let _ =
  Plugin_callback.add_abs_int (ref my_abs_int)
