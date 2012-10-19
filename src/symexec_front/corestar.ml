(********************************************************
   This file is part of coreStar
        src/symbfront/symbfront.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(* This file is a front end to the symbolic execution *)

open List
open Printf
open Core
open Pprinter_core
open Load_logic
open Psyntax

let question_file_name = ref "";;
let logic_file_name = ref "";;
let abduct_logic_file_name = ref "";;
let absrules_file_name = ref "";;

let set_question_file_name fn =
  question_file_name := fn;
  Symexec.file := Filename.basename fn

let arg_list = Config.args_default @ 
  [ ("-f", Arg.String set_question_file_name, "question file name" );
  ("-l", Arg.Set_string logic_file_name, "logic file name" );
  ("-al", Arg.Set_string abduct_logic_file_name, "abduction logic file name" );
  ("-a", Arg.Set_string absrules_file_name, "abstraction rules file name" );
]


let main () : unit = 
  let usage_msg = "Usage: -l <logic_file_name>  [-al <abduct_logic_file_name>]  -a <abstraction_file_name>  -f <question_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !question_file_name="" then 
    printf "Question file not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !absrules_file_name="" then
    printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
  else
    if !Config.smt_run then Smt.smt_init(); 
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;

    let l1,l2,cn = load_logic !logic_file_name in
    let lo = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let l1,l2,cn = Load_logic.load_abstractions !absrules_file_name in 
    let abs_rules = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    
    if !abduct_logic_file_name="" then
      let question_list = System.parse_file Parser.symb_question_file Lexer.token !question_file_name "Question" in
      List.iter (
      fun {proc_name=mname; proc_spec=spec; proc_body=core} ->
        Format.printf "Method: %s\nSpec: %a"  mname  Spec.spec2str spec; 
        let stmts_core = map Cfg_core.mk_node core in 
        if Symexec.verify mname stmts_core spec lo abs_rules then
        Format.printf "\nGood specification!\n\n" else Format.printf "\nBad specification!\n\n" 
      ) question_list     
    else
      let l1,l2,cn = load_logic !abduct_logic_file_name in
      let abduct_lo = {empty_logic with seq_rules=l1; rw_rules=l2; consdecl=cn} in
      let question_list = System.parse_file Parser.symb_question_file Lexer.token !question_file_name "Question" in
      List.iter (
      fun {proc_name=mname; proc_spec=spec; proc_body=core} ->
        Format.printf "\nMethod: %s\nSpec: %a"  mname  Spec.spec2str spec; 
        let stmts_core = map Cfg_core.mk_node core in 
        let specs = Symexec.bi_abduct mname stmts_core spec lo abduct_lo abs_rules in
        Format.printf "\nDiscovered specs:\n";
        List.iter (fun (spec_pre, spec_post) ->
          Format.printf "@\npre:@\n    %a@." Sepprover.string_inner_form spec_pre;
          Format.printf "@\npost:@\n    %a@." Sepprover.string_inner_form spec_post;)
          specs
      ) question_list

let _ =
  System.set_signal_handlers ();
  main ()
