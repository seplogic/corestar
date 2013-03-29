(** This is the main entry point for corestar. *)

open Corestar_std
open Format

let parse fn =
  System.parse_file Parser.symb_question_file Lexer.token fn "core"

let procedures = ref []
let parse_file f = procedures =:: parse f

let () =
  try
    procedures := [];
    Arg.parse Config.args_default parse_file "alt_abd [options] <files>";
    let q =
      { Core.q_procs = List.concat !procedures
      ; q_rules = Psyntax.empty_logic (* XXX *)
      ; q_infer = true
      ; q_name = "core_question" (* XXX: customize from cmdline *) } in
    if not (Symexec.verify q) then
      printf "@[verification failed@."
  with Symexec.Fatal m -> eprintf "@[ERROR: %s@." m
