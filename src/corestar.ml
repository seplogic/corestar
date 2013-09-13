(** This is the main entry point for corestar. *)

open Corestar_std
open Debug
open Format

module C = Core
module PA = ParserAst


(* NOTE: The lists of rules, procedures, etc, in the result are
reversed compared to the argument. *)
let question_of_entries xs =
  let add_abstraction r q =
    let q_rules = q.C.q_rules in let abstraction = q_rules.C.abstraction in
    let abstraction = r :: abstraction in
    let q_rules = { q_rules with C.abstraction } in { q with C.q_rules } in
  let add_calculus r q =
    let q_rules = q.C.q_rules in let calculus = q_rules.C.calculus in
    let calculus = r :: calculus in
    let q_rules = { q_rules with C.calculus } in { q with C.q_rules } in
  let f q = function
    | PA.AbstractionRule r -> add_abstraction r q
    | PA.CalculusRule r -> add_calculus r q
    | PA.Procedure p -> { q with C.q_procs = p :: q.C.q_procs } in
  let z =
    { CoreOps.empty_ast_question with C.q_infer = !Config.use_abduction } in
  List.fold_left f z xs

let path = System.getenv_dirlist (System.getenv "COREPATH")
let parse fn = System.parse_file Parser.file Lexer.token fn "core"

let load fn =
  let xs = Load.load ~path parse fn in
  let q = question_of_entries (List.rev xs) in
  { q with C.q_name = fn }

let verify fn =
  if log log_phase then fprintf logf "@[verifying file %s@." fn;
  try begin
    if Symexec.verify (load fn) then
      printf "@[%s: @{<g> OK@}@]@\n" fn
    else
      printf "@[%s: @{<b>NOK@}@]@\n" fn
  end with Symexec.Fatal m -> eprintf "@[ERROR: %s@." m

let () =
  printf "@["; eprintf "@[";
  Arg.parse Config.args_default verify "corestar [options] <files>";
  printf "@?"; eprintf "@?"
