(** This is the main entry point for corestar. *)

open Corestar_std
open Format

module C = Core
module PA = ParserAst
module PS = Psyntax


(* NOTE: The lists of rules, procedures, etc, in the result are
reversed compared to the argument. *)
let question_of_entries =
  let f q = function
    | PA.ProverQuery _ ->
        eprintf "@[WARNING: Ignoring prover query.@." (* TODO(rgrig) *);
        q
    | PA.Rule r -> { q with C.q_rules = PS.add_rule q.C.q_rules r }
    | PA.Procedure p -> { q with C.q_procs = p :: q.C.q_procs } in
  List.fold_left f CoreOps.empty_question

let path = System.getenv_dirlist (System.getenv "COREPATH")
let parse fn = System.parse_file Parser.file Lexer.token fn "core"
let load fn =
  let xs = Load.load ~path parse fn in
  let q = question_of_entries (List.rev xs) in
  { q with C.q_name = fn }

let verify fn =
  try if not (Symexec.verify (load fn)) then
    printf "@[%s: failed verification@]@\n" fn
  with Symexec.Fatal m -> eprintf "@[ERROR: %s@." m

let () =
  printf "@[";
  Arg.parse Config.args_default verify "alt_abd [options] <files>";
  printf "@]"
