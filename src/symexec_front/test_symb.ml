(********************************************************
   This file is part of coreStar
        src/symbfront/test_symb.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(* This file is a front end to the symbolic execution *)

open Core
open Format
open List
open Load_logic
open Psyntax

let question_file_name = ref "";;
let logic_file_name = ref "";;
let absrules_file_name = ref "";;

let set_question_file_name fn =
  question_file_name := fn;
  Symexec.file := Filename.basename fn

let proof_succes = ref true;;

let arg_list = Config.args_default @
  [ ("-f", Arg.String set_question_file_name, "question file name" );
  ("-l", Arg.Set_string logic_file_name, "logic file name" );
  ("-a", Arg.Set_string absrules_file_name, "abstraction rules file name" );
]


let main () : unit =
  let usage_msg = "Usage: -l <logic_file_name>  -a <abstraction_file_name>  -f <question_file_name>" in
  Arg.parse arg_list (fun s ->()) usage_msg;
  let args_ok, check_fn = let x = ref false in x, fun (f, m) ->
    if f = "" then eprintf "@[%s file name missing.@." m;
    x := false in
  List.iter check_fn [
    (!question_file_name, "Question");
    (!logic_file_name, "Logic");
    (!absrules_file_name, "Abstraction rules")];
  if not !args_ok then
    printf "@[ %s@\n@]" usage_msg
  else begin
    if !Config.smt_run then Smt.smt_init();
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;

    let l1,l2,cn = load_logic !logic_file_name in
    let lo = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let l1,l2,cn = Load_logic.load_logic !absrules_file_name in
    let abs_rules = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in

    let question_list =
      System.parse_file
          Parser.symb_test_file
          Lexer.token
          !question_file_name
          "Test" in
    printf "@[";
    List.iter (
    function ({proc_name=mname;proc_spec=spec;proc_body=core}, result) ->
      let core = match core with None -> assert false | Some core -> core in
      let cfg = map Cfg_core.mk_node core in
      let verify_one spec =
        Symexec.verify mname cfg spec lo abs_rules in
      let all_ok =
        HashSet.fold (fun spec ok -> ok && verify_one spec) spec true in
      if all_ok = result
      then printf "."
      else printf "@\nTest %s wrongly %s.@\n" mname
        (if result then "fails" else "passes")
    ) question_list;
    printf "@]"
  end

let _ =
  System.set_signal_handlers ();
  main ()
