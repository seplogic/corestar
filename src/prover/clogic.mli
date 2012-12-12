(********************************************************
   This file is part of coreStar
        src/prover/clogic.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)
exception Success
exception Failed
exception Assm_Contradiction
module RMSet : Multiset.S with type t = string * Cterm.term_handle
type multiset = RMSet.multiset
module SMSet : Multiset.S with type t = string * Psyntax.args list
type syntactic_form = {
  sspat : SMSet.multiset;
  splain : SMSet.multiset;
  sdisjuncts : (syntactic_form * syntactic_form) list;
  seqs : (Psyntax.args * Psyntax.args) list;
  sneqs : (Psyntax.args * Psyntax.args) list;
}
type formula = {
  spat : RMSet.multiset;
  plain : RMSet.multiset;
  disjuncts : (formula * formula) list;
  eqs : (Cterm.term_handle * Cterm.term_handle) list;
  neqs : (Cterm.term_handle * Cterm.term_handle) list;
}
module F:
  sig
    type ts_formula = {
      ts : Cterm.term_structure;
      form : formula;
    }
  end
val mk_ts_form : Cterm.term_structure -> formula -> F.ts_formula
val break_ts_form : F.ts_formula -> Cterm.term_structure * formula
val kill_var : F.ts_formula -> Vars.var -> F.ts_formula
val update_var_to : F.ts_formula -> Vars.var -> Psyntax.args -> F.ts_formula
val pp_ts_formula : Format.formatter -> F.ts_formula -> unit
val pp_syntactic_form : Format.formatter -> syntactic_form -> unit
val conjunction : formula -> formula -> formula
val empty : formula
val false_sform : syntactic_form
val truth : formula
val is_sempty : syntactic_form -> bool
val add_eqs_list : (Cterm.term_handle * Cterm.term_handle) list -> Cterm.term_structure -> Cterm.term_structure
val add_neqs_list : (Cterm.term_handle * Cterm.term_handle) list -> Cterm.term_structure -> Cterm.term_structure
val intersect_with_ts : Cterm.term_structure -> bool -> RMSet.multiset -> RMSet.multiset -> (RMSet.multiset * RMSet.multiset * RMSet.multiset)
val normalise :
  Cterm.term_structure -> formula -> formula * Cterm.term_structure
val convert_to_inner : Psyntax.pform -> syntactic_form
val convert_to_pform : syntactic_form -> Psyntax.pform
val conjoin : bool -> F.ts_formula -> syntactic_form -> F.ts_formula
type sequent = {
  matched : RMSet.multiset;
  ts : Cterm.term_structure;
  assumption : formula;
  obligation : formula;
  antiframe : formula; (* TODO(rgrig): Wat? Remove! *)
}
val plain : formula -> bool
val pp_sequent : Format.formatter -> sequent -> unit
val true_sequent : sequent -> bool
val frame_sequent : sequent -> bool
val abductive_sequent : sequent -> bool
type sequent_rule =
    Psyntax.psequent * Psyntax.psequent list list * string *
    (Psyntax.pform * Psyntax.pform) * Psyntax.where list
type pat_sequent = {
  assumption_same : syntactic_form;
  assumption_diff : syntactic_form;
  obligation_diff : syntactic_form;
  antiframe_diff : syntactic_form;
}
val convert_sf : bool -> Cterm.term_structure -> syntactic_form -> (formula * Cterm.term_structure)
val convert_sf_without_eqs : bool -> Cterm.term_structure -> syntactic_form -> (formula * Cterm.term_structure)
val convert_sequent : Psyntax.psequent -> pat_sequent
type inner_sequent_rule = {
  conclusion : pat_sequent;
  premises : pat_sequent list list;
  name : string;
  without_left : syntactic_form;
  without_right : syntactic_form;
  where : Psyntax.where list;
}
val convert_rule : sequent_rule -> inner_sequent_rule
val match_form : bool -> Cterm.term_structure -> formula -> syntactic_form ->
  ('a -> 'a -> 'a) -> (Cterm.term_structure * formula -> 'a) -> 'a
val apply_or_left : sequent -> sequent list
val apply_or_right : sequent -> sequent list list
val get_frame : sequent -> F.ts_formula
val get_frames : sequent list -> F.ts_formula list
val convert_with_eqs : bool -> Psyntax.pform -> F.ts_formula
val convert :
  bool ->
  Cterm.term_structure -> Psyntax.pform -> formula * Cterm.term_structure
val convert_ground : Cterm.term_structure -> syntactic_form -> (formula * Cterm.term_structure)
val make_implies : F.ts_formula -> Psyntax.pform -> sequent
val make_syntactic : F.ts_formula -> syntactic_form
val make_implies_inner : F.ts_formula -> F.ts_formula -> sequent
val ts_form_to_pform : F.ts_formula -> Psyntax.pform
val ts_form_to_pform_no_ts : F.ts_formula -> Psyntax.pform
val pform_to_ts_form : Psyntax.pform -> F.ts_formula

(* TODO(rgrig): Remove these. It's wrong to share equalities. *)
module AF:
  sig
    type ts_formula = {
      ts : Cterm.term_structure;
      form : formula;
      antiform : formula;
    }
  end
val mk_ts_form_af : Cterm.term_structure -> formula -> formula -> AF.ts_formula
val break_ts_form_af : AF.ts_formula -> Cterm.term_structure * formula * formula
val kill_var_af : AF.ts_formula -> Vars.var -> AF.ts_formula
val update_var_to_af : AF.ts_formula -> Vars.var -> Psyntax.args -> AF.ts_formula
val pp_ts_formula_af : Format.formatter -> AF.ts_formula -> unit
val conjoin_af : bool -> AF.ts_formula -> syntactic_form -> syntactic_form -> AF.ts_formula
val combine : bool -> F.ts_formula -> syntactic_form -> AF.ts_formula
val get_frames_antiframes : sequent list -> AF.ts_formula list
