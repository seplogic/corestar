(********************************************************
   This file is part of coreStar
        src/parsing/load_logic.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* File to read a logic file and its imports. *)
open Debug
open Format
open Load
open Psyntax
open System

let load_logic_extra_rules 
    dirs filename extra_rules 
    : (Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list) =
  let fileentrys =
    import_flatten_extra_rules dirs filename extra_rules Parser.rule_file Lexer.token in
  let rl = expand_equiv_rules fileentrys in 
  let sl,rm,cn = 
    List.fold_left
      (fun (sl,rm,cn) rule ->
	match rule with
        | ConsDecl(f) -> (sl,rm,f::cn)
	| SeqRule(r) -> (r::sl,rm,cn)
	| RewriteRule(r) -> (sl,r::rm,cn)
	| EquivRule(r) -> assert false)
      ([], [], []) 
      rl
  in
  if log log_load then
    fprintf logf "@[<2>Sequent rules%a@." (pp_list pp_sequent_rule) sl;
  (sl,rm,cn)

let load_logic_internal
    dirs filename 
    : (sequent_rule list * rewrite_rule list * string list) = 
  load_logic_extra_rules dirs filename []

let load_logic = load_logic_internal Cli_utils.logic_dirs
let load_abstractions = load_logic_internal Cli_utils.abs_dirs
