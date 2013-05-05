(** This is the main entry point for corestar. *)

open Corestar_std
open Debug
open Format

module C = Core
module PA = ParserAst
module PS = Psyntax

(*
(* rlp: Stolen from run_prover *)
let log_prove = true

let log x = true

let process_prover_query logic = function
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
    )
*)
    
(* NOTE: The lists of rules, procedures, etc, in the result are
reversed compared to the argument. *)
let question_of_entries =
  let f q = function
    | PA.ProverQuery pq ->
(*        process_prover_query pq; *)
        eprintf "@[WARNING: Ignoring prover query.@." (* TODO(rgrig) *);
        q
    | PA.Rule r -> { q with C.q_rules = PS.add_rule q.C.q_rules r }
    | PA.Procedure p -> { q with C.q_procs = p :: q.C.q_procs } in
  List.fold_left f { CoreOps.empty_question with C.q_infer = !Config.use_abduction_ref }

let path = System.getenv_dirlist (System.getenv "COREPATH")
let parse fn = System.parse_file Parser.file Lexer.token fn "core"
let load fn =
  let xs = Load.load ~path parse fn in
  let q = question_of_entries (List.rev xs) in
  { q with C.q_name = fn }

let verify fn =
  if !Config.smt_run then Smt.smt_init();

  if log log_specs then fprintf logf "@[Verifying %s...@." fn;
  try if not (Symexec.verify (load fn)) then
    printf "@[%s: failed verification@]@\n" fn
  with Symexec.Fatal m -> eprintf "@[ERROR: %s@." m

let () =
  printf "@[";
  Arg.parse Config.args_default verify "alt_abd [options] <files>";
  printf "@]"
