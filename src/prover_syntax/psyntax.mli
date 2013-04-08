(********************************************************
   This file is part of coreStar
        src/prover_syntax/psyntax.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

exception Contradiction
type args =
    Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * args list
  | Arg_cons of string * args list
  | Arg_record of (string * args) list
val mkArgRecord : (string * args) list -> args
type fldlist = (string * args) list
module VarSet : Set.S with type elt = Vars.var
type varset = VarSet.t
val vs_add : VarSet.elt -> VarSet.t -> VarSet.t
val vs_empty : VarSet.t
val vs_is_empty : VarSet.t -> bool
val vs_union : VarSet.t -> VarSet.t -> VarSet.t
val vs_inter : VarSet.t -> VarSet.t -> VarSet.t
val vs_diff : VarSet.t -> VarSet.t -> VarSet.t
val vs_fold : (VarSet.elt -> 'a -> 'a) -> VarSet.t -> 'a -> 'a
val vs_for_all : (VarSet.elt -> bool) -> VarSet.t -> bool
val vs_from_list : VarSet.elt list -> VarSet.t
module VarMap : Map.S with type key = Vars.var
type 'a varmap_t = 'a VarMap.t
type varmapargs = args varmap_t
module VarHash : Hashtbl.S with type key = Vars.var
type varhashargs = args VarHash.t
type 'a varhash_t = 'a VarHash.t
type varmap = Plain of varmapargs | Freshen of varmapargs * varhashargs
val find : VarMap.key -> varmap -> args
val add : VarMap.key -> args -> varmap -> varmap
val empty : varmap
val subst_args : varmap -> args -> args
val string_args : Format.formatter -> args -> unit
val string_args_list : Format.formatter -> args list -> unit
val ev_args : args -> VarSet.t -> VarSet.t
val ev_args_list : args list -> VarSet.t -> VarSet.t
val fv_args : args -> VarSet.t -> VarSet.t
val fv_args_list : args list -> VarSet.t -> VarSet.t
type pform_at =
    P_EQ of args * args
  | P_NEQ of args * args
  | P_PPred of string * args list
  | P_SPred of string * args list
  | P_Wand of pform * pform
  | P_Or of pform * pform
  | P_Septract of pform * pform
  | P_False
and pform = pform_at list
val pconjunction : pform -> pform -> pform
val ( &&& ) : pform -> pform -> pform
val subst_pform : varmap -> pform -> pform
type psequent =
  { ast_assumption_same : pform
  ; ast_assumption_diff : pform
  ; ast_obligation_diff : pform }
val mk_psequent : pform -> pform -> pform -> psequent
val purify : pform_at list -> pform_at list
val is_numerical_args : args -> bool
val is_numerical_pform_at : pform_at -> bool
type varterm = Var of varset
type where =
  | NotInContext of varterm
  | NotInTerm of varterm * args
  | PureGuard of pform
type sequent_rule =
    psequent * psequent list list * string * (pform * pform) * where list
val pp_sequent_rule : Format.formatter -> sequent_rule -> unit
type rewrite_guard = {
  without_form : pform;
  if_form : pform;
  rewrite_where : where list;
}
type rewrite_rule = {
  function_name : string;
  arguments : args list;
  result : args;
  guard : rewrite_guard;
  rewrite_name : string;
  saturate : bool;
}
type equiv_rule = string * pform * pform * pform * pform
type rules =
  | SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
  | EquivRule of equiv_rule
  | ConsDecl of string
type question =
    Implication of pform * pform
  | Inconsistency of pform
  | Frame of pform * pform
  | Equal of pform * args * args
  | Abs of pform
  | Abduction of pform * pform
type var = Vars.var
type term = args
type form = pform
val mkVar : var -> term
val mkFun : string -> term list -> term
val mkString : string -> term
val mkFalse : form
val mkEQ : term * term -> form
val mkNEQ : term * term -> form
val mkPPred : string * term list -> form
val mkSPred : string * term list -> form
val mkOr : form * form -> form
val mkStar : form -> form -> form
val mkEmpty : form
val fv_form : pform -> VarSet.t
val ev_form_acc : pform -> VarSet.t -> VarSet.t
val ev_form : pform -> VarSet.t
val string_form : form pretty_printer
val string_form_at : pform_at pretty_printer
val prog_var : string -> var
val fresh_exists_var : unit -> var
type variable_subst = varmap
val empty_subst : variable_subst
val add_subst : var -> term -> variable_subst -> variable_subst
val subst_kill_vars_to_fresh_prog : varset -> variable_subst
val subst_kill_vars_to_fresh_exist : varset -> variable_subst
val subst_form : variable_subst -> form -> form
val mk_seq_rule : psequent * psequent list list * string -> sequent_rule
type logic = {
  seq_rules : sequent_rule list;
  rw_rules : rewrite_rule list;
  consdecl : string list;
}
val empty_logic : logic
val add_rule : logic -> rules -> logic
