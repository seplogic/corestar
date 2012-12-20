(********************************************************
   This file is part of coreStar
        src/proverfront/run.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Congruence
open Debug
open Format
open Load_logic
open Psyntax

let program_file_name = ref "";;
let logic_file_name = ref "";;

let arg_list = Config.args_default @
  [ ("-f", Arg.Set_string(program_file_name), "program file name");
    ("-l", Arg.Set_string(logic_file_name), "logic file name"); ]


let main () =
  let usage_msg="Usage: -f <file_name> -l <logic_file_name>" in
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !program_file_name="" then
    printf "File name not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else
    if !Config.smt_run then Smt.smt_init();
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;

    let l1,l2,cn = load_logic !logic_file_name in
    let logic = {empty_logic with seq_rules = l1; rw_rules=l2; consdecl = cn} in
(*    let s = System.string_of_file !program_file_name  in*)
    let question_list = System.parse_file Parser.question_file Lexer.token !program_file_name "Questions" in

    List.iter (
    fun question ->
      match question with
    | Psyntax.Implication (heap1,heap2) ->
	printf "Check implication\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	if (Sepprover.implies_opt logic (Sepprover.convert heap1) heap2)
	then printf("Holds!\n\n") else printf("Does not hold!\n\n");
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Frame (heap1, heap2)  ->
	printf "Find frame for\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	let x = Sepprover.frame_opt logic
	    (Sepprover.convert heap1) heap2 in

	(match x with None -> printf "Can't find frame!" | Some x -> List.iter (fun form -> printf "Frame:\n %a\n" Sepprover.string_inner_form  form) x);
	printf "\n";
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Abs (heap1)  ->
	printf "Abstract@\n  @[%a@]@\nresults in@\n  " Psyntax.string_form heap1;
	let x = Sepprover.abs_opt logic (Sepprover.convert heap1) in
	List.iter (fun form -> printf "%a\n" Sepprover.string_inner_form form) x;
	printf "\n";
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Inconsistency (heap1) ->
	if Sepprover.inconsistent_opt logic (Sepprover.convert heap1)
	then printf("Inconsistent!\n\n") else printf("Consistent!\n\n");
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Equal (heap,arg1,arg2) -> ()

    | Psyntax.Abduction (heap1, heap2)  ->
      Format.printf "Find antiframe for\n %a\n ===> \n %a \n"
      Psyntax.string_form heap1   Psyntax.string_form heap2;
      let x = (Sepprover.abduct_inner logic (Sepprover.convert heap1) heap2) in
      (match x with
        | None -> Format.printf "Can't find antiframe!\n"
        | Some ls ->
          List.iter (fun (a, f) ->
            Format.printf "(%a,%a)@\n@\n"
            Sepprover.string_inner_form a Sepprover.string_inner_form f) ls;
      );

(*	if Prover.check_equal logic heap arg1 arg2
	then Printf.printf("Equal!\n\n") else Printf.printf("Not equal!\n\n")*)
(*    | _ -> Printf.printf "Currently unsupported" *)
  )
      question_list

let _ = main ()
